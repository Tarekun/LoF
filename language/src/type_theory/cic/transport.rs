use super::cic::CicTerm::{
    Abstraction, Application, Let, Match, Meta, Proj, Product, Sort, Variable,
};
use super::cic::{Cic, CicTerm, GLOBAL_INDEX, PLACEHOLDER_DBI};
use super::cic_utils::{
    apply_arguments, application_args, get_applied_function, get_arg_types,
    get_prod_innermost, is_instance_of, substitute,
};
use crate::error::LofError;
use std::collections::HashMap;
use crate::type_theory::commons::transport::EquivConfig;
use crate::type_theory::commons::utils::eta_expand;
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::{Kernel, Reducer, Refiner};

/// Mechanically transports a proof or function body about `config.type_a`
/// into the corresponding term about `config.type_b`, following Ringer,
/// Porter, Yazdani, Leo & Grossman, "Proof Repair across Type Equivalences"
/// (PUMPKIN Pi, arXiv:2010.00774): constructor applications of `type_a`
/// are rewritten to their `dep_constr` image, applications of `type_a`'s
/// auto-generated eliminator (`e_<type_a>`) are rewritten to `dep_elim`,
/// and any already-`transport`-ed auxiliary `fun`/`global` is substituted
/// via `lifted_names` - everything else recurses structurally, which is
/// what rewrites a quantifier `forall x:type_a. ...` into `forall
/// x:type_b. ...` without any separate "translate the statement" pass.
///
/// Scope: this only handles terms built as direct compositions of
/// `e_<Type>` eliminator applications, constructors and ordinary function
/// calls - not raw surface `match` expressions over `type_a` (see the
/// `Match` case below, and `docs/language/systems/transport.md` for why).
/// Every proof this engine is exercised against (`library/bin.lof`,
/// `library/vec.lof`) is written in that style for exactly that reason.
pub fn transport_term(
    environment: &mut Environment<Cic>,
    config: &EquivConfig<Cic>,
    term: &CicTerm,
) -> Result<CicTerm, LofError> {
    transport_term_inner(environment, config, term, &mut vec![])
}

/// `known_params` carries (name, original pre-transport type) for every
/// binder enclosing the current position. It exists so the `Match` case can
/// tell whether a scrutinee is `type_a`-typed without type-checking it
/// against the live environment: a lambda-bound parameter isn't registered
/// there (this kernel resolves variables by name through the environment,
/// and transport walks a term without introducing its binders), so that
/// check would silently answer "no" and let an untransportable `match`
/// through.
fn transport_term_inner(
    environment: &mut Environment<Cic>,
    config: &EquivConfig<Cic>,
    term: &CicTerm,
    known_params: &mut Vec<(String, CicTerm)>,
) -> Result<CicTerm, LofError> {
    match term {
        Sort(_) | Meta(_) => Ok(term.to_owned()),

        // `Proj` never appears in a source proof (it has no surface
        // syntax); it can only turn up if a term was normalized after the
        // kernel eta-expanded something. Transport it structurally.
        Proj(type_name, field_index, target) => Ok(Proj(
            type_name.to_owned(),
            *field_index,
            Box::new(transport_term_inner(
                environment,
                config,
                target,
                known_params,
            )?),
        )),

        Variable(name, dbi) => {
            if name == &config.type_a {
                Ok(Variable(config.type_b.clone(), *dbi))
            } else if let Some(new_name) = config.lifted_names.get(name) {
                Ok(Variable(new_name.clone(), *dbi))
            } else if *dbi == GLOBAL_INDEX
                && is_constructor_of(environment, &config.type_a, name)
            {
                dep_constr_of(config, name)
            } else {
                Ok(term.to_owned())
            }
        }

        Abstraction(var_name, var_type, body) => {
            let transported_type =
                transport_term_inner(environment, config, var_type, known_params)?;
            known_params.push((var_name.to_owned(), (**var_type).to_owned()));
            let transported_body =
                transport_term_inner(environment, config, body, known_params);
            known_params.pop();

            Ok(Abstraction(
                var_name.to_owned(),
                Box::new(transported_type),
                Box::new(transported_body?),
            ))
        }

        Product(var_name, domain, codomain) => {
            let transported_domain =
                transport_term_inner(environment, config, domain, known_params)?;
            known_params.push((var_name.to_owned(), (**domain).to_owned()));
            let transported_codomain =
                transport_term_inner(environment, config, codomain, known_params);
            known_params.pop();

            Ok(Product(
                var_name.to_owned(),
                Box::new(transported_domain),
                Box::new(transported_codomain?),
            ))
        }

        Let(var_name, var_type, body, scope) => {
            let var_type = match &**var_type {
                Some(t) => Some(transport_term_inner(
                    environment,
                    config,
                    t,
                    known_params,
                )?),
                None => None,
            };
            Ok(Let(
                var_name.to_owned(),
                Box::new(var_type),
                Box::new(transport_term_inner(
                    environment,
                    config,
                    body,
                    known_params,
                )?),
                Box::new(transport_term_inner(
                    environment,
                    config,
                    scope,
                    known_params,
                )?),
            ))
        }

        Application(_, _) => {
            let head = get_applied_function(term);
            let args = application_args(term);
            let transported_args = args
                .iter()
                .map(|arg| {
                    transport_term_inner(environment, config, arg, known_params)
                })
                .collect::<Result<Vec<_>, _>>()?;

            match &head {
                Variable(name, dbi) if *dbi == GLOBAL_INDEX => {
                    if is_constructor_of(environment, &config.type_a, name) {
                        Ok(apply_arguments(
                            &dep_constr_of(config, name)?,
                            transported_args,
                        ))
                    } else if let Some(new_name) =
                        config.lifted_names.get(name)
                    {
                        Ok(apply_arguments(
                            &Variable(new_name.to_owned(), GLOBAL_INDEX),
                            transported_args,
                        ))
                    } else if *name == format!("e_{}", config.type_a) {
                        let repaired = repair_minor_premises(
                            environment,
                            config,
                            &transported_args,
                        )?;
                        Ok(apply_arguments(&config.dep_elim, repaired))
                    } else {
                        // still transport the head: it may be the source
                        // type former itself (`List(T)` -> `PackedVec(T)`)
                        Ok(apply_arguments(
                            &transport_term_inner(
                                environment,
                                config,
                                &head,
                                known_params,
                            )?,
                            transported_args,
                        ))
                    }
                }
                _ => {
                    let transported_head = transport_term_inner(
                        environment,
                        config,
                        &head,
                        known_params,
                    )?;
                    Ok(apply_arguments(&transported_head, transported_args))
                }
            }
        }

        Match(scrutinee, branches) => {
            // A raw `match` on a `type_a`-typed scrutinee has no direct
            // DepConstr/DepElim-based rewrite here (unlike an explicit
            // `e_<type_a>(...)` application, whose motive and
            // per-constructor cases are ordinary sub-terms that transport
            // like anything else, or a top-level recursion split, which
            // `transport_definition` converts). `type_a`'s constructors
            // need not correspond to constructors of `type_b` at all, so
            // rewriting the patterns through DepConstr would produce a
            // `match` whose "patterns" aren't constructors. Fail loudly
            // instead - see the module doc comment.
            if is_type_a_scrutinee(
                environment,
                config,
                scrutinee,
                known_params,
            ) {
                return Err(LofError::custom(format!(
                    "transport: equivalence '{}' cannot transport a raw `match` over '{}' - rewrite the source proof/function to use e_{} explicitly instead",
                    config.name, config.type_a, config.type_a
                )));
            }

            let transported_scrutinee = transport_term_inner(
                environment,
                config,
                scrutinee,
                known_params,
            )?;
            let transported_branches = branches
                .iter()
                .map(|(pattern, body)| {
                    Ok((
                        transport_term_inner(
                            environment,
                            config,
                            pattern,
                            known_params,
                        )?,
                        transport_term_inner(
                            environment,
                            config,
                            body,
                            known_params,
                        )?,
                    ))
                })
                .collect::<Result<Vec<_>, LofError>>()?;

            Ok(Match(
                Box::new(transported_scrutinee),
                transported_branches,
            ))
        }
    }
}

//########################### IOTA REPAIR
//
/// Repairs the minor premises of a `dep_elim` application - the third of
/// PUMPKIN Pi's four configuration components, Iota.
///
/// A source proof by induction discharges each case using the source
/// type's *definitional* computation rules: `plus_z_r`'s base case is
/// `refl(Nat,z)`, a proof only because `plus(z,z)` reduces to `z`. After
/// transport the corresponding step is frequently only *propositional* -
/// `plus_bin(bz,bz)` does not reduce to `bz`, because `plus_bin` is built
/// from a `dep_elim` (`bin_succ_induction`) that has no computational
/// behaviour of its own. The transported case is then a well-formed term
/// of the wrong type, and the whole transport fails on unification.
///
/// `iota[c]` supplies exactly the missing equation: `dep_elim` applied at
/// `dep_constr(c)` equals the corresponding case. This rewrites each
/// premise's expected type along it, via `e_Eq` (this kernel's J), so the
/// already-transported term proves the goal the target side actually
/// states.
///
/// Premises that already type check are returned untouched, so an
/// equivalence whose target computes on its own (`ListPackedVec`, whose
/// `iota` table is empty) is unaffected.
fn repair_minor_premises(
    environment: &mut Environment<Cic>,
    config: &EquivConfig<Cic>,
    transported_args: &[CicTerm],
) -> Result<Vec<CicTerm>, LofError> {
    let param_count = environment
        .get_inductive_param_count(&config.type_a)
        .unwrap_or(0);
    let Some(constructors) =
        environment.constructor_store.get(&config.type_a).cloned()
    else {
        return Ok(transported_args.to_vec());
    };

    // layout: params.., motive, one case per constructor, [target]. The
    // application may be partial - a proof by induction is routinely
    // written without its target, as `∀n. ..` rather than `λn. ..`
    if transported_args.len() < param_count + 1 {
        return Ok(transported_args.to_vec());
    }
    let case_count = constructors
        .len()
        .min(transported_args.len() - param_count - 1);
    if case_count == 0 {
        return Ok(transported_args.to_vec());
    }

    // instantiate dep_elim's own type at the parameters and the transported
    // motive, so each remaining Pi layer states one case's expected type in
    // concrete terms
    // Without dep_elim's type there is nothing to check the premises
    // against; leave them exactly as transported and let any genuine
    // mismatch surface as an ordinary type error later.
    let Ok(mut remaining) = Cic::type_check_term(&config.dep_elim, environment)
    else {
        return Ok(transported_args.to_vec());
    };
    for supplied in transported_args.iter().take(param_count + 1) {
        let Product(binder, _, codomain) = remaining else {
            return Ok(transported_args.to_vec());
        };
        remaining = substitute(&codomain, &binder, supplied);
    }

    let mut repaired = transported_args.to_vec();
    for (case_index, (constructor_name, _)) in
        constructors.iter().enumerate().take(case_count)
    {
        let Product(binder, expected_type, codomain) = remaining.to_owned()
        else {
            break;
        };

        let slot = param_count + 1 + case_index;
        repaired[slot] = repair_premise(
            environment,
            config,
            constructor_name,
            &repaired[slot],
            &expected_type,
        )?;

        remaining = substitute(&codomain, &binder, &repaired[slot]);
    }

    Ok(repaired)
}
//
//
/// Repairs one minor premise against the type `dep_elim` expects of it.
///
/// Walks under the premise's binders in step with the expected type's Pi
/// chain - the rewrite has to happen *inside* them, since the equation
/// mentions the case's own arguments (`iota[s]` speaks about
/// `bin_succ(b)`, and `b` is the step case's own binder) - then, if the
/// body's actual type already matches, changes nothing.
fn repair_premise(
    environment: &mut Environment<Cic>,
    config: &EquivConfig<Cic>,
    constructor_name: &str,
    premise: &CicTerm,
    expected: &CicTerm,
) -> Result<CicTerm, LofError> {
    let mut binders: Vec<(String, CicTerm)> = vec![];
    let mut body = premise.to_owned();
    let mut goal = expected.to_owned();

    while let (
        Abstraction(premise_binder, _, premise_body),
        Product(expected_binder, domain, codomain),
    ) = (&body, &goal)
    {
        // keep the premise's own binder names: they are what its body
        // actually refers to, whereas the expected type's names come from
        // `dep_elim`'s declaration
        binders
            .push((premise_binder.to_owned(), (**domain).to_owned()));
        let renamed = substitute(
            codomain,
            expected_binder,
            &Variable(premise_binder.to_owned(), PLACEHOLDER_DBI),
        );
        let next_body = (**premise_body).to_owned();
        goal = renamed;
        body = next_body;
    }

    let repaired_body =
        environment.with_local_assumptions(&binders, |environment| {
            repair_body(environment, config, constructor_name, &body, &goal)
        })?;

    // nothing to do: hand the premise back exactly as it was
    if repaired_body == body {
        return Ok(premise.to_owned());
    }

    Ok(eta_expand::<Cic, _>(&binders, &repaired_body, |(name, ty), acc| {
        Abstraction(name, Box::new(ty), Box::new(acc))
    }))
}
//
//
/// The innermost step of `repair_premise`: `body` is expected to prove
/// `goal`. If it already does, it is returned unchanged. Otherwise the
/// constructor's `iota` entry is instantiated into an equation and used to
/// rewrite `goal` into the proposition `body` does prove.
fn repair_body(
    environment: &mut Environment<Cic>,
    config: &EquivConfig<Cic>,
    constructor_name: &str,
    body: &CicTerm,
    goal: &CicTerm,
) -> Result<CicTerm, LofError> {
    let Ok(actual) = Cic::type_check_term(body, environment) else {
        // the premise doesn't type check on its own; let the ordinary
        // failure path report it rather than guessing at a rewrite
        return Ok(body.to_owned());
    };
    if Cic::types_unify(environment, &actual, goal).is_ok() {
        return Ok(body.to_owned());
    }

    let Some(iota) = config.iota.get(constructor_name) else {
        // no bridging equation was declared for this constructor: fall
        // through to the ordinary type error, which names the mismatch
        return Ok(body.to_owned());
    };

    // `iota` is stated in `dep_elim`'s own binders (motive, cases, the
    // constructor's arguments); instantiate it at whatever is in scope here
    // by unifying its equation's left-hand side against a redex of the goal
    // Two different vocabularies are in play. The rule speaks about
    // `dep_elim` applied at a DepConstr image; the goal writes the same
    // thing as a call to the lifted function (`plus_bin`). Matching needs
    // them reconciled - but the *result* must stay in the goal's own
    // vocabulary, because it ends up inside an `e_Eq` motive the kernel
    // then type checks, and inlining definitions there is ruinously
    // expensive: type checking a curried application re-checks its whole
    // function spine, so nesting multiplies rather than adds.
    //
    // So: unfold the lifted names into a scratch copy, recover the rule's
    // instantiation from that, then locate the redex back in the folded
    // goal by *convertibility* and rewrite there.
    let goal = beta_normalize(goal);
    let unfolded_goal = unfold_lifted_names(environment, config, &goal);
    let Some((equation_type, left, right, proof)) =
        instantiate_iota(environment, iota, &unfolded_goal)
    else {
        return Ok(body.to_owned());
    };

    // rewrite the goal right-to-left: `body` proves the goal with the
    // redex already replaced by `right`, and J run along the rule turns
    // that into a proof of the goal itself
    let normalized_left = Cic::normalize_term(environment, &left);
    let Some((abstracted, occurrence)) = abstract_convertible_occurrence(
        environment,
        &goal,
        &normalized_left,
        "_iota_rewrite_target",
    ) else {
        return Ok(body.to_owned());
    };

    Ok(build_eq_rewrite(
        &equation_type,
        // the folded spelling of `left`, so the emitted term stays in the
        // goal's own vocabulary
        &occurrence,
        &right,
        "_iota_rewrite_target",
        &abstracted,
        &goal,
        body,
        &proof,
    ))
}
//
//
/// Instantiates a declared `iota` entry into a concrete equation
/// `(type, lhs, rhs, proof)` usable at the current goal.
///
/// The entry is a lemma quantified over `dep_elim`'s motive and cases and
/// the constructor's own arguments; the goal fixes all of them. Its
/// equation's left-hand side is `dep_elim` applied at that constructor's
/// DepConstr image - a rigid head with the quantified variables sitting in
/// argument positions - so the instantiation is recovered by ordinary
/// first-order matching against a sub-term of the goal, not by search.
///
/// Both sides stay folded: the caller has already unfolded the lifted
/// names in the goal, which is the only difference in vocabulary between
/// the two. Keeping everything else folded matters because whatever this
/// recovers becomes the rule's instantiation, and so ends up inside a term
/// the kernel type checks.
fn instantiate_iota(
    environment: &mut Environment<Cic>,
    iota: &CicTerm,
    goal: &CicTerm,
) -> Option<(CicTerm, CicTerm, CicTerm, CicTerm)> {
    let iota_type = Cic::type_check_term(iota, environment).ok()?;

    // peel the lemma's quantifiers, then read its equation off the body
    let mut binder_names = vec![];
    let mut remaining = iota_type;
    while let Product(binder, _, codomain) = remaining {
        binder_names.push(binder);
        remaining = (*codomain).to_owned();
    }
    let (equation_type, pattern_left, _) = as_equation(&remaining)?;

    for candidate in subterms(goal) {
        let mut bindings = HashMap::new();
        if !first_order_match(
            &pattern_left,
            &candidate,
            &binder_names,
            &mut bindings,
        ) {
            continue;
        }
        let Some(arguments) = binder_names
            .iter()
            .map(|name| bindings.get(name).cloned())
            .collect::<Option<Vec<_>>>()
        else {
            // the match left some quantifier undetermined: this sub-term
            // is not actually an instance of the rule
            continue;
        };

        let instance = apply_arguments(iota, arguments);
        let instance_type =
            Cic::type_check_term(&instance, environment).ok()?;
        let (instance_equation_type, left, right) =
            as_equation(&instance_type)?;
        let _ = equation_type;

        return Some((instance_equation_type, left, right, instance));
    }

    None
}
//
//
/// Beta (and let) reduction only - no unfolding of definitions, no
/// eliminator computation. Used to instantiate a `dep_elim` premise type
/// (the motive applied to a DepConstr image) without inlining every
/// definition it mentions, which full normalization would do.
pub(crate) fn beta_normalize(term: &CicTerm) -> CicTerm {
    match term {
        Application(left, right) => {
            let left = beta_normalize(left);
            let right = beta_normalize(right);
            match left {
                Abstraction(binder, _, body) => {
                    beta_normalize(&substitute(&body, &binder, &right))
                }
                _ => Application(Box::new(left), Box::new(right)),
            }
        }
        Abstraction(name, domain, body) => Abstraction(
            name.to_owned(),
            Box::new(beta_normalize(domain)),
            Box::new(beta_normalize(body)),
        ),
        Product(name, domain, body) => Product(
            name.to_owned(),
            Box::new(beta_normalize(domain)),
            Box::new(beta_normalize(body)),
        ),
        Proj(type_name, field_index, target) => Proj(
            type_name.to_owned(),
            *field_index,
            Box::new(beta_normalize(target)),
        ),
        Let(name, _, body, scope) => {
            beta_normalize(&substitute(scope, name, body))
        }
        _ => term.to_owned(),
    }
}
//
//
/// Replaces every already-transported auxiliary name in `term` by its
/// definition, then beta-reduces. This is the *only* unfolding done before
/// matching an iota rule: the rule is stated in terms of `dep_elim`, while
/// a transported goal calls the lifted function that was built from it.
fn unfold_lifted_names(
    environment: &Environment<Cic>,
    config: &EquivConfig<Cic>,
    term: &CicTerm,
) -> CicTerm {
    let mut unfolded = term.to_owned();
    for lifted in config.lifted_names.values() {
        if let Some((_, definition)) = environment.get_from_deltas(lifted) {
            unfolded = substitute(&unfolded, lifted, &definition);
        }
    }

    beta_normalize(&unfolded)
}
//
//
/// Like `abstract_occurrence`, but a sub-term counts as an occurrence when
/// it is *convertible* to `needle` rather than syntactically equal - the
/// goal writes the redex as `plus_bin(..)` where the rule writes it as the
/// `dep_elim` application that unfolds to.
///
/// Returns both the abstracted goal and the occurrence *as the goal spells
/// it*, so the caller can keep the emitted proof term folded.
///
/// `needle` is expected to be already normalized; each candidate is
/// normalized once and compared. Only application-shaped nodes are tested:
/// the left-hand side of a `dep_elim` computation rule is always an
/// application, and testing every node would mean a normalization per
/// variable.
pub(crate) fn abstract_convertible_occurrence(
    environment: &mut Environment<Cic>,
    haystack: &CicTerm,
    needle: &CicTerm,
    fresh_name: &str,
) -> Option<(CicTerm, CicTerm)> {
    fn walk(
        environment: &mut Environment<Cic>,
        haystack: &CicTerm,
        needle: &CicTerm,
        fresh_name: &str,
        found: &mut Option<CicTerm>,
    ) -> CicTerm {
        if matches!(haystack, Application(_, _))
            && &Cic::normalize_term(environment, haystack) == needle
        {
            *found = Some(haystack.to_owned());
            return Variable(fresh_name.to_string(), PLACEHOLDER_DBI);
        }

        match haystack {
            Application(left, right) => Application(
                Box::new(walk(environment, left, needle, fresh_name, found)),
                Box::new(walk(environment, right, needle, fresh_name, found)),
            ),
            Abstraction(name, domain, body) => Abstraction(
                name.to_owned(),
                Box::new(walk(environment, domain, needle, fresh_name, found)),
                Box::new(walk(environment, body, needle, fresh_name, found)),
            ),
            Product(name, domain, body) => Product(
                name.to_owned(),
                Box::new(walk(environment, domain, needle, fresh_name, found)),
                Box::new(walk(environment, body, needle, fresh_name, found)),
            ),
            Proj(type_name, field_index, target) => Proj(
                type_name.to_owned(),
                *field_index,
                Box::new(walk(environment, target, needle, fresh_name, found)),
            ),
            _ => haystack.to_owned(),
        }
    }

    let mut found = None;
    let abstracted =
        walk(environment, haystack, needle, fresh_name, &mut found);
    found.map(|occurrence| (abstracted, occurrence))
}
//
//
/// First-order matching of `pattern` against `term`, where the names in
/// `binder_names` are the pattern's variables. Each is bound to whatever
/// sits in its position, and a name occurring twice must be matched by the
/// same term both times.
pub(crate) fn first_order_match(
    pattern: &CicTerm,
    term: &CicTerm,
    binder_names: &[String],
    bindings: &mut HashMap<String, CicTerm>,
) -> bool {
    if let Variable(name, _) = pattern {
        if binder_names.contains(name) {
            return match bindings.get(name) {
                Some(already) => already == term,
                None => {
                    bindings.insert(name.to_owned(), term.to_owned());
                    true
                }
            };
        }
    }

    match (pattern, term) {
        (Variable(left, _), Variable(right, _)) => left == right,
        (Sort(left), Sort(right)) => left == right,
        (Meta(left), Meta(right)) => left == right,
        (
            Application(pattern_left, pattern_right),
            Application(term_left, term_right),
        ) => {
            first_order_match(
                pattern_left,
                term_left,
                binder_names,
                bindings,
            ) && first_order_match(
                pattern_right,
                term_right,
                binder_names,
                bindings,
            )
        }
        (
            Abstraction(_, pattern_domain, pattern_body),
            Abstraction(_, term_domain, term_body),
        )
        | (
            Product(_, pattern_domain, pattern_body),
            Product(_, term_domain, term_body),
        ) => {
            first_order_match(
                pattern_domain,
                term_domain,
                binder_names,
                bindings,
            ) && first_order_match(
                pattern_body,
                term_body,
                binder_names,
                bindings,
            )
        }
        (
            Proj(pattern_type, pattern_field, pattern_target),
            Proj(term_type, term_field, term_target),
        ) => {
            pattern_type == term_type
                && pattern_field == term_field
                && first_order_match(
                    pattern_target,
                    term_target,
                    binder_names,
                    bindings,
                )
        }
        (
            Match(pattern_scrutinee, pattern_branches),
            Match(term_scrutinee, term_branches),
        ) => {
            pattern_branches.len() == term_branches.len()
                && first_order_match(
                    pattern_scrutinee,
                    term_scrutinee,
                    binder_names,
                    bindings,
                )
                && pattern_branches.iter().zip(term_branches.iter()).all(
                    |((_, pattern_body), (_, term_body))| {
                        // patterns bind their own variables; only the
                        // branch bodies are matchable
                        first_order_match(
                            pattern_body,
                            term_body,
                            binder_names,
                            bindings,
                        )
                    },
                )
        }
        _ => false,
    }
}
//
//
/// Every sub-term of `term`, outermost first - the candidate redexes
/// `instantiate_iota` matches its rule against.
fn subterms(term: &CicTerm) -> Vec<CicTerm> {
    let mut collected = vec![term.to_owned()];
    match term {
        Application(left, right) => {
            collected.extend(subterms(left));
            collected.extend(subterms(right));
        }
        Abstraction(_, domain, body) | Product(_, domain, body) => {
            collected.extend(subterms(domain));
            collected.extend(subterms(body));
        }
        Proj(_, _, target) => collected.extend(subterms(target)),
        Match(scrutinee, branches) => {
            collected.extend(subterms(scrutinee));
            for (_, body) in branches {
                collected.extend(subterms(body));
            }
        }
        Let(_, _, body, scope) => {
            collected.extend(subterms(body));
            collected.extend(subterms(scope));
        }
        _ => {}
    }
    collected
}
//
//
/// Reads `Eq(T, lhs, rhs)` off a type, if that is what it is.
fn as_equation(term: &CicTerm) -> Option<(CicTerm, CicTerm, CicTerm)> {
    match get_applied_function(term) {
        Variable(name, _) if name == "Eq" => {
            let args = application_args(term);
            match args.as_slice() {
                [equation_type, left, right] => Some((
                    equation_type.to_owned(),
                    left.to_owned(),
                    right.to_owned(),
                )),
                _ => None,
            }
        }
        _ => None,
    }
}
//
//
/// A rewrite along `proof : Eq(T, from, to)`, turning `payload`, which
/// proves `abstracted[to]`, into a proof of `goal` (= `abstracted[from]`).
///
/// Note the direction: the equation reads left-to-right but the rewrite
/// runs right-to-left, because `iota` says what `dep_elim` *computes to*
/// while the goal is stated in terms of `dep_elim` itself.
///
/// Rather than composing a `sym` with a rewrite - two nested `e_Eq`
/// applications - this eliminates once, into a *function*:
///
/// ```text
/// e_Eq(T, from, λy.λ_. abstracted[y] -> goal, (λx:goal. x), to, proof)
///   : abstracted[to] -> goal
/// ```
///
/// which is then applied to `payload`. At `y := from` the motive is
/// `goal -> goal`, discharged by the identity; at `y := to` it is exactly
/// the coercion wanted. Halving the nesting this way is not cosmetic:
/// type checking a curried application re-checks its whole function spine,
/// so nested applications multiply rather than add.
#[allow(clippy::too_many_arguments)]
fn build_eq_rewrite(
    equation_type: &CicTerm,
    from: &CicTerm,
    to: &CicTerm,
    abstracted_name: &str,
    abstracted_goal: &CicTerm,
    goal: &CicTerm,
    payload: &CicTerm,
    proof: &CicTerm,
) -> CicTerm {
    let bound =
        Variable(abstracted_name.to_string(), PLACEHOLDER_DBI);

    let motive = Abstraction(
        abstracted_name.to_string(),
        Box::new(equation_type.to_owned()),
        Box::new(Abstraction(
            "_rewrite_h".to_string(),
            Box::new(apply_arguments(
                &Variable("Eq".to_string(), GLOBAL_INDEX),
                vec![
                    equation_type.to_owned(),
                    from.to_owned(),
                    bound,
                ],
            )),
            Box::new(Product(
                "_rewrite_x".to_string(),
                Box::new(abstracted_goal.to_owned()),
                Box::new(goal.to_owned()),
            )),
        )),
    );

    let coercion =
        apply_arguments(&Variable("e_Eq".to_string(), GLOBAL_INDEX), vec![
            equation_type.to_owned(),
            from.to_owned(),
            motive,
            Abstraction(
                "_rewrite_x".to_string(),
                Box::new(goal.to_owned()),
                Box::new(Variable(
                    "_rewrite_x".to_string(),
                    PLACEHOLDER_DBI,
                )),
            ),
            to.to_owned(),
            proof.to_owned(),
        ]);

    Application(Box::new(coercion), Box::new(payload.to_owned()))
}
//########################### IOTA REPAIR

/// Whether `scrutinee` is known to have type `config.type_a`. Prefers the
/// locally tracked binder types (see `transport_term_inner`), falling back
/// to the environment for anything not bound by an enclosing binder (a
/// global, say).
fn is_type_a_scrutinee(
    environment: &mut Environment<Cic>,
    config: &EquivConfig<Cic>,
    scrutinee: &CicTerm,
    known_params: &[(String, CicTerm)],
) -> bool {
    if let Variable(name, _) = scrutinee {
        if let Some((_, declared_type)) = known_params
            .iter()
            .rev()
            .find(|(param_name, _)| param_name == name)
        {
            return is_instance_of(declared_type, &config.type_a);
        }
    }

    Cic::type_check_term(scrutinee, environment)
        .map(|scrutinee_type| {
            is_instance_of(&scrutinee_type, &config.type_a)
        })
        .unwrap_or(false)
}

/// Transports a `fun`/`global` definition, handling the one shape
/// `transport_term` alone cannot: a top-level `fun rec`-style body
/// structurally recursing on a `type_a`-typed parameter via a raw
/// `match`. This exists because this kernel's auto-generated eliminators
/// have no reduction rule of their own (`e_<Type>` never ι-reduces, even
/// applied to a concrete constructor) - so a function *defined* via direct
/// eliminator application would never compute, which defeats the purpose
/// of transporting an ordinary, computing function like `plus`/`len`/
/// `map`. Those must stay `match`-based to actually reduce, so transport
/// needs to convert the `match` into a `dep_elim` application itself.
///
/// Scope: handles exactly `fun rec F(p_1,...,p_k):R { match p_i with |
/// ctor(rec_args) => body }`, where `p_i` is `type_a`-typed and every
/// self-recursive call in a branch body has the shape `F(rec_arg, ...)`
/// (`rec_arg` a strict structural sub-part of `p_i`, the remaining
/// arguments passed through unchanged) - covering ordinary structural
/// recursion on one argument, exactly as used by every function in this
/// codebase's own library (`plus`, `len`, `map`). A call whose other
/// arguments are themselves transformed, mutual recursion, or recursion
/// nested under a *second* `match`, is out of scope (see
/// `docs/language/systems/transport.md`) - falls back to `transport_term`,
/// which will error if it still can't make sense of the term.
pub fn transport_definition(
    environment: &mut Environment<Cic>,
    config: &EquivConfig<Cic>,
    fun_name: &str,
    new_type: &CicTerm,
    term: &CicTerm,
) -> Result<CicTerm, LofError> {
    transport_definition_inner(
        environment,
        config,
        fun_name,
        new_type,
        term,
        &mut vec![],
    )
}

/// `known_params` tracks (name, original pre-transport type) for every
/// enclosing lambda peeled off so far, so the recursion-match detection
/// below never needs to type-check the (possibly still-unbound, per this
/// kernel's name-based-only variable resolution) scrutinee against the
/// live environment - it just looks its declared type up directly.
fn transport_definition_inner(
    environment: &mut Environment<Cic>,
    config: &EquivConfig<Cic>,
    fun_name: &str,
    new_type: &CicTerm,
    term: &CicTerm,
    known_params: &mut Vec<(String, CicTerm)>,
) -> Result<CicTerm, LofError> {
    match term {
        Abstraction(var_name, var_type, body) => {
            let transported_var_type = transport_term_inner(
                environment,
                config,
                var_type,
                known_params,
            )?;
            known_params.push((var_name.to_owned(), (**var_type).to_owned()));
            let transported_body = transport_definition_inner(
                environment,
                config,
                fun_name,
                new_type,
                body,
                known_params,
            )?;
            known_params.pop();
            Ok(Abstraction(
                var_name.to_owned(),
                Box::new(transported_var_type),
                Box::new(transported_body),
            ))
        }

        Match(scrutinee, branches) => {
            let is_recursion_match = match scrutinee.as_ref() {
                Variable(name, _) => known_params
                    .iter()
                    .rev()
                    .find(|(param_name, _)| param_name == name)
                    .map(|(_, original_type)| {
                        is_instance_of(original_type, &config.type_a)
                    })
                    .unwrap_or(false),
                _ => false,
            };

            if !is_recursion_match {
                return transport_term_inner(
                    environment,
                    config,
                    term,
                    known_params,
                );
            }

            let final_result_type = get_prod_innermost(new_type).to_owned();
            let constructors = environment
                .constructor_store
                .get(&config.type_a)
                .cloned()
                .ok_or_else(|| {
                    LofError::custom(format!(
                        "transport: no registered constructors for '{}'",
                        config.type_a
                    ))
                })?;

            // A parameterized source type (`List(T)`) means its eliminator
            // - and so `dep_elim` - takes those parameters before the
            // motive, and its per-constructor cases do *not* rebind them.
            // Recover them from the scrutinee's own declared type.
            let param_count = environment
                .get_inductive_param_count(&config.type_a)
                .unwrap_or(0);
            let scrutinee_type = scrutinee_declared_type(scrutinee, known_params);
            let param_values: Vec<CicTerm> = match &scrutinee_type {
                Some(declared) => {
                    let applied = application_args(declared);
                    if applied.len() < param_count {
                        return Err(LofError::custom(format!(
                            "transport: scrutinee of type '{}' does not supply its {} parameter(s)",
                            config.type_a, param_count
                        )));
                    }
                    applied[..param_count].to_vec()
                }
                None if param_count == 0 => vec![],
                None => {
                    return Err(LofError::custom(format!(
                        "transport: cannot determine the parameters of '{}' for this match",
                        config.type_a
                    )))
                }
            };
            let transported_params = param_values
                .iter()
                .map(|value| {
                    transport_term_inner(environment, config, value, known_params)
                })
                .collect::<Result<Vec<_>, LofError>>()?;

            let mut minor_premises = vec![];
            for (ctor_name, ctor_type) in &constructors {
                minor_premises.push(build_minor_premise(
                    environment,
                    config,
                    fun_name,
                    branches,
                    ctor_name,
                    ctor_type,
                    &final_result_type,
                    param_count,
                    &transported_params,
                )?);
            }

            // the motive's domain is the *applied* target type
            // (`PackedVec(Tp)`), not the bare type former
            let motive_domain = apply_arguments(
                &Variable(config.type_b.clone(), GLOBAL_INDEX),
                transported_params.clone(),
            );
            let motive = Abstraction(
                "_transported_scrutinee".to_string(),
                Box::new(motive_domain),
                Box::new(final_result_type),
            );
            let transported_scrutinee = transport_term_inner(
                environment,
                config,
                scrutinee,
                known_params,
            )?;

            let mut dep_elim_args = transported_params;
            dep_elim_args.push(motive);
            dep_elim_args.extend(minor_premises);
            dep_elim_args.push(transported_scrutinee);

            Ok(apply_arguments(&config.dep_elim, dep_elim_args))
        }

        _ => transport_term_inner(environment, config, term, known_params),
    }
}

/// The names bound by a term's leading Pi-chain, outermost first.
fn get_binder_names(term: &CicTerm) -> Vec<String> {
    let mut names = vec![];
    let mut current = term;
    while let Product(binder, _, codomain) = current {
        names.push(binder.to_owned());
        current = codomain;
    }
    names
}

/// The declared (pre-transport) type of `scrutinee`, when it is one of the
/// binders tracked while walking into the term. Used to recover a
/// parameterized source type's parameter values (`List(T)` -> `[T]`).
fn scrutinee_declared_type(
    scrutinee: &CicTerm,
    known_params: &[(String, CicTerm)],
) -> Option<CicTerm> {
    match scrutinee {
        Variable(name, _) => known_params
            .iter()
            .rev()
            .find(|(param_name, _)| param_name == name)
            .map(|(_, declared)| declared.to_owned()),
        _ => None,
    }
}

/// Builds one `dep_elim` minor premise from the branch of `branches`
/// matching `ctor_name`, per the scheme described on `transport_definition`.
#[allow(clippy::too_many_arguments)]
fn build_minor_premise(
    environment: &mut Environment<Cic>,
    config: &EquivConfig<Cic>,
    fun_name: &str,
    branches: &[(CicTerm, CicTerm)],
    ctor_name: &str,
    ctor_type: &CicTerm,
    final_result_type: &CicTerm,
    param_count: usize,
    param_values: &[CicTerm],
) -> Result<CicTerm, LofError> {
    let (pattern, body) = branches
        .iter()
        .find(|(pattern, _)| {
            get_applied_function(pattern)
                == Variable(ctor_name.to_string(), GLOBAL_INDEX)
        })
        .cloned()
        .ok_or_else(|| {
            LofError::custom(format!(
                "transport: fun '{}' has no branch for constructor '{}'",
                fun_name, ctor_name
            ))
        })?;

    let pattern_arg_names: Vec<String> = application_args(&pattern)
        .iter()
        .filter_map(|arg| match arg {
            Variable(n, _) => Some(n.clone()),
            _ => None,
        })
        .collect();
    let ctor_arg_types = get_arg_types(ctor_type);

    let mut transported_body = body;

    // A pattern in this language spells out the type's parameters too
    // (`cons(A, h, ll)`), but the eliminator's case doesn't rebind them -
    // they're fixed once, before the motive. Drop those leading slots and
    // substitute the parameter values for their names, so a branch body
    // mentioning `A` still refers to the right thing.
    let skipped = param_count.min(pattern_arg_names.len());
    for (param_name, param_value) in
        pattern_arg_names.iter().take(skipped).zip(param_values.iter())
    {
        transported_body =
            substitute(&transported_body, param_name, param_value);
    }
    let pattern_arg_names = &pattern_arg_names[skipped..];
    let ctor_arg_types = if ctor_arg_types.len() >= skipped {
        ctor_arg_types[skipped..].to_vec()
    } else {
        ctor_arg_types
    };

    // The remaining argument types are stated in terms of the *constructor's
    // own* parameter binders (`cons : ΠT:TYPE. T -> List(T) -> List(T)`
    // leaves `T` in `List(T)`), which nothing binds once the parameter slots
    // are dropped. Instantiate them with the actual parameter values.
    let constructor_param_names: Vec<String> = get_binder_names(ctor_type)
        .into_iter()
        .take(param_count)
        .collect();
    let ctor_arg_types: Vec<CicTerm> = ctor_arg_types
        .iter()
        .map(|arg_type| {
            constructor_param_names
                .iter()
                .zip(param_values.iter())
                .fold(arg_type.to_owned(), |acc, (param_name, param_value)| {
                    substitute(&acc, param_name, param_value)
                })
        })
        .collect();

    let mut binders: Vec<(String, CicTerm)> = vec![];
    for (arg_name, arg_type) in
        pattern_arg_names.iter().zip(ctor_arg_types.iter())
    {
        let is_recursive = is_instance_of(arg_type, &config.type_a);
        let transported_arg_type =
            transport_term(environment, config, arg_type)?;
        binders.push((arg_name.clone(), transported_arg_type));

        if is_recursive {
            let ih_name = format!("ih_{}", arg_name);
            transported_body = replace_self_call(
                &transported_body,
                fun_name,
                arg_name,
                &ih_name,
            );
            binders.push((ih_name, final_result_type.clone()));
        }
    }

    let transported_body = transport_term(environment, config, &transported_body)?;

    Ok(eta_expand::<Cic, _>(
        &binders,
        &transported_body,
        |(name, ty), acc| Abstraction(name, Box::new(ty), Box::new(acc)),
    ))
}

/// Replaces every occurrence of `fun_name(rec_arg_name, ...)` (a
/// self-recursive call on the given recursive pattern variable) with a
/// bare reference to `ih_name` - the induction hypothesis standing in for
/// "what the transported self-call would produce". Only matches a call
/// whose *first* argument is exactly `rec_arg_name`; see
/// `transport_definition`'s doc comment for the scope this implies.
fn replace_self_call(
    term: &CicTerm,
    fun_name: &str,
    rec_arg_name: &str,
    ih_name: &str,
) -> CicTerm {
    if matches!(term, Application(_, _)) {
        let head = get_applied_function(term);
        let args = application_args(term);
        // any argument position may hold the recursive sub-term: it is
        // the first for `plus(nn, m)`, but the second for a function that
        // takes the element type first, as `len(T, ll)` does
        let recurses_on_sub_term = args.iter().any(
            |arg| matches!(arg, Variable(n, _) if n == rec_arg_name),
        );
        if head == Variable(fun_name.to_string(), GLOBAL_INDEX)
            && recurses_on_sub_term
        {
            return Variable(ih_name.to_string(), PLACEHOLDER_DBI);
        }
    }

    match term {
        Application(left, right) => Application(
            Box::new(replace_self_call(left, fun_name, rec_arg_name, ih_name)),
            Box::new(replace_self_call(
                right,
                fun_name,
                rec_arg_name,
                ih_name,
            )),
        ),
        Abstraction(var_name, var_type, body) => Abstraction(
            var_name.to_owned(),
            Box::new(replace_self_call(
                var_type,
                fun_name,
                rec_arg_name,
                ih_name,
            )),
            Box::new(replace_self_call(body, fun_name, rec_arg_name, ih_name)),
        ),
        Product(var_name, domain, codomain) => Product(
            var_name.to_owned(),
            Box::new(replace_self_call(
                domain,
                fun_name,
                rec_arg_name,
                ih_name,
            )),
            Box::new(replace_self_call(
                codomain,
                fun_name,
                rec_arg_name,
                ih_name,
            )),
        ),
        Match(matched_term, branches) => Match(
            Box::new(replace_self_call(
                matched_term,
                fun_name,
                rec_arg_name,
                ih_name,
            )),
            branches
                .iter()
                .map(|(pattern, body)| {
                    (
                        pattern.clone(),
                        replace_self_call(
                            body,
                            fun_name,
                            rec_arg_name,
                            ih_name,
                        ),
                    )
                })
                .collect(),
        ),
        Let(var_name, var_type, body, scope) => Let(
            var_name.to_owned(),
            Box::new((**var_type).as_ref().map(|t| {
                replace_self_call(t, fun_name, rec_arg_name, ih_name)
            })),
            Box::new(replace_self_call(body, fun_name, rec_arg_name, ih_name)),
            Box::new(replace_self_call(
                scope,
                fun_name,
                rec_arg_name,
                ih_name,
            )),
        ),
        _ => term.to_owned(),
    }
}

fn is_constructor_of(
    environment: &Environment<Cic>,
    type_name: &str,
    ctor_name: &str,
) -> bool {
    environment
        .get_constructors_for(type_name)
        .map(|constructors| constructors.contains(ctor_name))
        .unwrap_or(false)
}

fn dep_constr_of(
    config: &EquivConfig<Cic>,
    ctor_name: &str,
) -> Result<CicTerm, LofError> {
    config.dep_constr.get(ctor_name).cloned().ok_or_else(|| {
        LofError::custom(format!(
            "transport: equivalence '{}' has no dep_constr entry for constructor '{}' of '{}'",
            config.name, ctor_name, config.type_a
        ))
    })
}

#[cfg(test)]
#[path = "../../tests/type_theory/cic/transport.rs"]
mod tests;
