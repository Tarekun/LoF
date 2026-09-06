use super::cic::CicTerm::{
    Abstraction, Application, Let, Match, Meta, Product, Sort, Variable,
};
use super::cic::{Cic, CicTerm, GLOBAL_INDEX, PLACEHOLDER_DBI};
use super::cic_utils::{
    apply_arguments, application_args, get_applied_function, get_arg_types,
    get_prod_innermost, is_instance_of, substitute,
};
use crate::error::LofError;
use crate::type_theory::commons::transport::EquivConfig;
use crate::type_theory::commons::utils::eta_expand;
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::Kernel;

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
                        Ok(apply_arguments(
                            &config.dep_elim,
                            transported_args,
                        ))
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
