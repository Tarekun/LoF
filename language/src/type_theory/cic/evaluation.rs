use super::cic::CicStm::{Axiom, Fun, Global, Theorem};
use super::cic::CicTerm::{
    Abstraction, Application, Let, Match, Proj, Product, Sort, Variable,
};
use super::cic::{Cic, CicStm, CicTerm, NameKind};
use super::cic_utils::make_multiarg_fun_type;
use crate::error::LofError;
use crate::type_theory::cic::cic_utils::{
    application_args, apply_arguments, get_applied_function, index_variables,
    is_instance_of, substitute,
};
use crate::type_theory::cic::type_check::inductive_eliminator;
use crate::type_theory::commons::evaluation::{
    evaluate_axiom, evaluate_fun, evaluate_global, evaluate_theorem,
    reduce_application, reduce_let, reduce_variable,
};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::{Kernel, Refiner};
use std::collections::HashMap;

//########################### TERM βδ-REDUCTION
pub fn one_step_reduction(
    environment: &Environment<Cic>,
    term: &CicTerm,
) -> CicTerm {
    match term {
        Variable(var_name, _) => {
            reduce_variable::<Cic>(environment, var_name, term)
        }
        Application(left, right) => {
            if let Some(iota_reduced) = try_iota_reduction(environment, term) {
                iota_reduced
            } else {
                reduce_application::<Cic, _, _>(
                    environment,
                    left,
                    right,
                    |fun_reduced| match fun_reduced {
                        Abstraction(var_name, _, body) => {
                            Some((var_name.to_string(), (**body).to_owned()))
                        }
                        _ => None,
                    },
                    |left_reduced, right_reduced| {
                        Application(
                            Box::new(left_reduced),
                            Box::new(right_reduced),
                        )
                    },
                )
            }
        }
        Let(var_name, var_type, body, scope) => {
            reduce_let(environment, var_name, var_type, body, scope)
        }
        Match(matched_term, branches) => {
            reduce_match(environment, matched_term, branches)
        }
        Proj(type_name, field_index, target) => {
            reduce_proj(environment, type_name, *field_index, target)
        }
        // Descend into a dependent function type's domain/codomain (resp.
        // an abstraction's domain/body) so a redex embedded there - eg a
        // motive applied to a bound variable, exactly what an eliminator's
        // generated minor-premise/conclusion types produce - gets reduced
        // too. Without this, two Pi-types that are only equal up to
        // reducing an under-binder application (the routine case for any
        // dependent induction proof) are never recognized as such, since
        // unification normalizes both sides before comparing them.
        //
        // Note these take a *single* step on each component rather than
        // normalizing it outright: `generic_term_normalization` already
        // iterates to a fixed point, so a nested full normalization here
        // would redo that inner fixpoint on every outer iteration, making
        // the total work exponential in the term's binder depth.
        Product(var_name, domain, codomain) => Product(
            var_name.to_string(),
            Box::new(one_step_reduction(environment, domain)),
            Box::new(one_step_reduction(environment, codomain)),
        ),
        Abstraction(var_name, domain, body) => Abstraction(
            var_name.to_string(),
            Box::new(one_step_reduction(environment, domain)),
            Box::new(one_step_reduction(environment, body)),
        ),
        _ => term.clone(),
    }
}
//
//
/// Whether `type_name` admits η-conversion: whether an *opaque* value of
/// it may be treated as literally being an application of its single
/// constructor to its own fields. Returns that constructor's name and
/// type, plus how many fields it has beyond the type's parameters.
///
/// Three conditions, each load-bearing:
///
/// - **Exactly one constructor.** Otherwise there is no canonical shape to
///   expand into.
/// - **No indices** (the type former's arity is exhausted by its
///   parameters). This one is a soundness condition, not conservatism:
///   `Eq` is single-constructor, and η for it would say every proof of
///   `Eq(T,x,y)` *is* `refl` - ie hand us UIP/axiom K for free.
/// - **No recursive occurrence** among the constructor's own arguments.
///   For a recursive type the expansion feeds a sub-term of the same type
///   straight back into the rule, so normalization would not terminate.
///
/// `PackedVec(T) := pack(∀n:Nat. Vec(T,n) -> PackedVec(T))` satisfies all
/// three; `Vec` (indexed), `Eq` (indexed) and `List` (two constructors,
/// recursive) satisfy none.
fn eta_eligible_constructor(
    environment: &Environment<Cic>,
    type_name: &str,
) -> Option<(String, CicTerm, usize)> {
    let constructors = environment.get_constructor_signatures(type_name)?;
    if constructors.len() != 1 {
        return None;
    }
    let (constructor_name, constructor_type) = &constructors[0];

    let param_count = environment.get_inductive_param_count(type_name)?;

    // no indices: every Pi layer of the type former's own type is a
    // parameter
    let (_, type_former) = environment.get_from_context(type_name)?;
    let mut former_arity = 0;
    let mut remaining = &type_former;
    while let Product(_, _, codomain) = remaining {
        former_arity += 1;
        remaining = codomain;
    }
    if former_arity != param_count {
        return None;
    }

    // no recursive occurrence among the constructor's arguments
    let mut field_count = 0;
    let mut remaining = constructor_type;
    let mut depth = 0;
    while let Product(_, domain, codomain) = remaining {
        if depth >= param_count {
            if is_instance_of(domain, type_name) {
                return None;
            }
            field_count += 1;
        }
        depth += 1;
        remaining = codomain;
    }

    Some((
        constructor_name.to_owned(),
        constructor_type.to_owned(),
        field_count,
    ))
}
//
//
/// η-expands an opaque `target` of the η-eligible type `type_name` into
/// `C(params.., target.0, .., target.k-1)`, the fields being `Proj` nodes.
///
/// The caller supplies `params` because they are not recoverable from an
/// opaque target - but both call sites have them to hand already (an
/// eliminator application from its own leading arguments, a `match` from
/// its pattern's leading slots, which β-reduction has already rewritten to
/// the actual parameter values).
///
/// Returns `None` when the type is not η-eligible, which is also how the
/// two call sites keep their previous "genuinely stuck" behaviour.
fn eta_expand_target(
    environment: &Environment<Cic>,
    type_name: &str,
    params: &[CicTerm],
    target: &CicTerm,
) -> Option<CicTerm> {
    let (constructor_name, _, field_count) =
        eta_eligible_constructor(environment, type_name)?;

    let mut args = params.to_vec();
    for field_index in 0..field_count {
        args.push(Proj(
            type_name.to_string(),
            field_index,
            Box::new(target.to_owned()),
        ));
    }

    Some(apply_arguments(
        &Variable(constructor_name, NameKind::Const()),
        args,
    ))
}
//
//
/// ι-reduction for a projection: `C(params.., a_0..a_k).i` computes to
/// `a_i`. On anything else - notably an opaque variable, which is the
/// whole reason `Proj` exists - the projection is its own normal form.
///
/// Note this rule deliberately does *not* η-expand its own target: that is
/// what stops `x -> C(x.0, x.1) -> C(C(x.0.0, ..).0, ..)` from running
/// forever.
fn reduce_proj(
    environment: &Environment<Cic>,
    type_name: &str,
    field_index: usize,
    target: &CicTerm,
) -> CicTerm {
    // A single step, not a full normalization: `one_step_reduction`'s
    // caller already iterates to a fixed point, so normalizing here would
    // redo the whole sub-term's reduction on every one of those rounds.
    let normalized_target = one_step_reduction(environment, target);

    let rebuilt = || {
        Proj(
            type_name.to_string(),
            field_index,
            Box::new(normalized_target.to_owned()),
        )
    };

    let Some((constructor_name, _, _)) =
        eta_eligible_constructor(environment, type_name)
    else {
        return rebuilt();
    };
    let Some(param_count) = environment.get_inductive_param_count(type_name)
    else {
        return rebuilt();
    };

    match get_applied_function(&normalized_target) {
        Variable(name, NameKind::Const()) if name == constructor_name => {
            let args = application_args(&normalized_target);
            match args.get(param_count + field_index) {
                Some(field) => field.to_owned(),
                None => rebuilt(),
            }
        }
        _ => rebuilt(),
    }
}
//
//
/// ι-reduction for an auto-generated eliminator: given a fully applied
/// `e_<Type>(params.., motive, case_1..case_k, instance)` whose `instance`
/// is a concrete constructor application `ctor_i(params.., args..)`,
/// computes to `case_i` applied to those args, with an inductive hypothesis.
///
/// A reference can be Inductive Definitions in the System Coq: Rules and
/// Properties by Paulin
fn try_iota_reduction(
    environment: &Environment<Cic>,
    term: &CicTerm,
) -> Option<CicTerm> {
    /// The inductive type corresponding to the eliminator used
    fn eliminated_type(term: &CicTerm) -> Option<String> {
        match get_applied_function(term) {
            Variable(name, NameKind::Const()) => {
                Some(name.strip_prefix("e_")?.to_string())
            }
            _ => None,
        }
    }

    /// Splits the used constructor's name and the supplied arguments
    fn split_instance(instance: &CicTerm) -> Option<(String, Vec<CicTerm>)> {
        match get_applied_function(instance) {
            Variable(name, NameKind::Const()) => {
                Some((name, application_args(instance)))
            }
            _ => None,
        }
    }

    /// Returns argument types from constructor_type, reduced by `supplied_args`
    /// by walking down `constructor_type`s Π chain
    fn supplied_arg_types(
        constructor_type: &CicTerm,
        supplied_args: &[CicTerm],
    ) -> Option<Vec<CicTerm>> {
        let mut arg_types = vec![];
        let mut remaining_type = constructor_type.to_owned();

        for supplied in supplied_args {
            match remaining_type {
                Product(binder, domain, codomain) => {
                    arg_types.push(*domain);
                    remaining_type = substitute(&codomain, &binder, supplied);
                }
                // fewer Pi layers than supplied arguments: not a shape this
                // rule understands
                _ => return None,
            }
        }

        Some(arg_types)
    }

    fn inductive_hypothesis(
        type_name: &str,
        leading_args: &[CicTerm],
        param_count: usize,
        occurrence: &CicTerm,
        occurrence_type: &CicTerm,
    ) -> Option<CicTerm> {
        let occurrence_args = application_args(occurrence_type);
        if occurrence_args.len() < param_count {
            return None;
        }

        let mut hypothesis_args = leading_args.to_vec();
        hypothesis_args.extend_from_slice(&occurrence_args[param_count..]);
        // recursive occurance pushed as last arg for the eliminator
        // ie the instance the eliminator is applied to
        hypothesis_args.push(occurrence.to_owned());

        Some(apply_arguments(
            //TODO i need to review this im not sure why ud need to reuse
            //the eliminator here instead of the motive
            &Variable(format!("e_{}", type_name), NameKind::Const()),
            hypothesis_args,
        ))
    }

    let type_name = eliminated_type(term)?;
    let param_count = environment.get_inductive_param_count(&type_name)?;
    let constructors = environment.get_constructor_signatures(&type_name)?;

    // #params + motive + #cases + instance
    let fixed_args = param_count + 1 + constructors.len() + 1;
    let args = application_args(term);
    // partial application nothing to compute
    if args.len() < fixed_args {
        return None;
    }

    let supplied_instance = args.last()?;
    // The instance isn't constructor-headed (eg a bound variable). For an
    // η-eligible type that is not actually stuck: every value of a
    // one-constructor, index-free, non-recursive type *is* an application
    // of that constructor to its own fields, so expand it and carry on.
    // For anything else it is genuinely stuck.
    let eta_expanded = match get_applied_function(supplied_instance) {
        Variable(_, NameKind::Const()) => None,
        _ => eta_expand_target(
            environment,
            &type_name,
            &args[..param_count],
            supplied_instance,
        ),
    };
    let instance = eta_expanded.as_ref().unwrap_or(supplied_instance);

    let (constructor_name, instance_args) = split_instance(instance)?;
    if instance_args.len() < param_count {
        return None;
    }
    let constructor_index = constructors
        .iter()
        .position(|(name, _)| name == &constructor_name)?;
    let arg_types =
        supplied_arg_types(&constructors[constructor_index].1, &instance_args)?;

    // left params are already fixed by the eliminator's own arguments, only
    // whats past them is fed to the case
    let own_args = &instance_args[param_count..];
    let own_arg_types = &arg_types[param_count..];
    // every argument except the instance, used for inductive hypothesis
    let leading_args = &args[..param_count + 1 + constructors.len()];

    // take the case corresponding to instance and apply arguments from the constructor (+IH)
    let mut reduced = args[param_count + 1 + constructor_index].to_owned();
    for (own_arg, own_arg_type) in own_args.iter().zip(own_arg_types.iter()) {
        reduced = Application(Box::new(reduced), Box::new(own_arg.to_owned()));

        // in case own_arg_type is this inductive type add an inductive hypothesis
        if is_instance_of(own_arg_type, &type_name) {
            let hypothesis = inductive_hypothesis(
                &type_name,
                leading_args,
                param_count,
                own_arg,
                own_arg_type,
            )?;
            reduced = Application(Box::new(reduced), Box::new(hypothesis));
        }
    }

    Some(reduced)
}
//
//
fn reduce_match(
    environment: &Environment<Cic>,
    matched_term: &CicTerm,
    branches: &Vec<(CicTerm, CicTerm)>,
) -> CicTerm {
    // As in `reduce_proj`: one step per round, letting the caller's
    // fixed-point loop do the iterating. Fully normalizing the scrutinee
    // here re-walks it once per round of that loop, which turns a term
    // with matches nested n deep into n-fold repeated work - and eta
    // expansion (below) produces exactly such nesting.
    let normalized_term = one_step_reduction(environment, matched_term);
    for (pattern, body) in branches {
        if matches_pattern(&normalized_term, pattern) {
            return substitute_pattern_variables(
                &normalized_term,
                pattern,
                body,
            );
        }
    }

    // No branch matched, but the scrutinee may still be η-expandable: if
    // this match is over a one-constructor, index-free, non-recursive
    // type, an opaque scrutinee *is* an application of that constructor to
    // its own fields. The matched type is read off the branch's own
    // pattern head rather than inferred, and the pattern's leading slots
    // supply the parameters (β-reduction has already rewritten them to the
    // actual values).
    if let Some((pattern, body)) = branches.first() {
        if let Variable(pattern_head, _) = get_applied_function(pattern) {
            if let Some(type_name) =
                environment.constructor_type_of(&pattern_head)
            {
                if let Some(param_count) =
                    environment.get_inductive_param_count(&type_name)
                {
                    let pattern_args = application_args(pattern);
                    if pattern_args.len() >= param_count {
                        if let Some(expanded) = eta_expand_target(
                            environment,
                            &type_name,
                            &pattern_args[..param_count],
                            &normalized_term,
                        ) {
                            if matches_pattern(&expanded, pattern) {
                                return substitute_pattern_variables(
                                    &expanded, pattern, body,
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    // The scrutinee normalized to something that isn't headed by any of
    // this match's constructors - eg an open/bound variable (as happens
    // routinely inside an inductive proof's step case, where the scrutinee
    // is a locally-bound predecessor rather than a concrete constructor
    // application). This is a stuck redex, not an error: exhaustiveness
    // over the matched type's constructors is already enforced separately
    // at type-checking time (`type_check_match`), so a *concrete*
    // (constructor-headed) scrutinee is always covered by some branch;
    // only an irreducible/open scrutinee can reach here, and the match
    // itself is its normal form.
    Match(Box::new(normalized_term), branches.to_owned())
}
//########################### TERM βδ-REDUCTION

//########################### STATEMENTS EXECUTION
pub fn evaluate_statement(
    environment: &mut Environment<Cic>,
    stm: &CicStm,
) -> Result<(), LofError> {
    match stm {
        Axiom(axiom_name, formula) => {
            evaluate_axiom::<Cic>(environment, axiom_name, formula)
        }
        Global(var_name, var_type, body) => {
            evaluate_global::<Cic>(environment, var_name, var_type, body)
        }
        Fun(fun_name, args, out_type, body, is_rec) => {
            evaluate_fun::<Cic, _, _>(
                environment,
                fun_name,
                args,
                out_type,
                body,
                is_rec,
                |args, out_type| make_multiarg_fun_type(args, out_type),
                |(var_name, var_type), body| {
                    Abstraction(var_name, Box::new(var_type), Box::new(body))
                },
            )
        }
        Theorem(theorem_name, formula, proof) => {
            evaluate_theorem::<Cic, CicTerm>(
                environment,
                theorem_name,
                formula,
                proof,
            )
        }
        CicStm::InductiveDef(type_name, params, ariety, constructors) => {
            evaluate_inductive(
                environment,
                type_name,
                params,
                ariety,
                constructors,
            )
        }
        CicStm::Equivalence(
            name,
            type_a,
            type_b,
            forward,
            backward,
            section,
            retraction,
            dep_elim,
            eta,
            dep_constr,
            iota,
        ) => evaluate_equivalence(
            environment,
            name,
            type_a,
            type_b,
            forward,
            backward,
            section,
            retraction,
            dep_elim,
            eta,
            dep_constr,
            iota,
        ),
        CicStm::Transport(new_name, new_type, old_name, equiv_name) => {
            evaluate_transport(
                environment,
                new_name,
                new_type,
                old_name,
                equiv_name,
            )
        }
    }
}
//
//
/// Registers a hand-authored type equivalence (see `EquivConfig`) into the
/// environment, so later `transport` statements in the same file can find
/// it by name.
#[allow(clippy::too_many_arguments)]
pub fn evaluate_equivalence(
    environment: &mut Environment<Cic>,
    name: &str,
    type_a: &CicTerm,
    type_b: &CicTerm,
    forward: &CicTerm,
    backward: &CicTerm,
    section: &CicTerm,
    retraction: &CicTerm,
    dep_elim: &CicTerm,
    eta: &Option<Box<CicTerm>>,
    dep_constr: &Vec<(String, CicTerm)>,
    iota: &Vec<(String, CicTerm)>,
) -> Result<(), LofError> {
    let type_a_name = match type_a {
        Variable(type_name, _) => type_name.to_owned(),
        _ => {
            return Err(LofError::custom(format!(
                "equivalence '{}': type_a must be a bare type name",
                name
            )))
        }
    };
    let type_b_name = match type_b {
        Variable(type_name, _) => type_name.to_owned(),
        _ => {
            return Err(LofError::custom(format!(
                "equivalence '{}': type_b must be a bare type name",
                name
            )))
        }
    };

    let config = EquivConfig {
        name: name.to_string(),
        type_a: type_a_name,
        type_b: type_b_name,
        forward: forward.to_owned(),
        backward: backward.to_owned(),
        section: section.to_owned(),
        retraction: retraction.to_owned(),
        dep_constr: dep_constr.iter().cloned().collect(),
        dep_elim: dep_elim.to_owned(),
        eta: eta.as_ref().map(|term| (**term).to_owned()),
        iota: iota.iter().cloned().collect(),
        lifted_names: HashMap::new(),
    };

    environment.add_equivalence(name, config);
    Ok(())
}
//
//
/// Performs the actual transport: retrieves `old_name`'s proof/definition
/// term, walks it via `transport_term`, validates the result type-checks
/// against the declared `new_type`, and registers `new_name` - as a new
/// theorem if `new_type` is `PROP`-sorted, as a new computational
/// definition otherwise (in which case `old_name -> new_name` is recorded
/// in the equivalence's `lifted_names`, so later transports of proofs
/// calling `old_name` pick up `new_name` instead).
pub fn evaluate_transport(
    environment: &mut Environment<Cic>,
    new_name: &str,
    new_type: &CicTerm,
    old_name: &str,
    equiv_name: &str,
) -> Result<(), LofError> {
    let config = environment.get_equivalence(equiv_name).cloned().ok_or_else(
        || {
            LofError::custom(format!(
                "transport: unknown equivalence '{}'",
                equiv_name
            ))
        },
    )?;

    // A theorem's witness lives in `theorem_proofs` (it stays opaque for
    // reduction, unlike a `fun`/`global` body, which is a delta); try
    // that first and fall back to `deltas` since `old_name` may be either.
    let old_term = environment
        .get_theorem_proof(old_name)
        .or_else(|| environment.get_from_deltas(old_name).map(|(_, term)| term))
        .ok_or_else(|| {
            LofError::custom(format!(
                "transport: '{}' has no known proof/definition term to transport (not a checked theorem, fun, or global)",
                old_name
            ))
        })?;

    let transported = transport_definition(
        environment,
        &config,
        old_name,
        new_type,
        &old_term,
    )?;
    let transported = index_variables(&transported);

    let transported_type = Cic::type_check_term(&transported, environment)?;
    Cic::types_unify(environment, &transported_type, new_type)?;

    let target_sort = Cic::type_check_term(new_type, environment)?;
    let is_theorem = matches!(target_sort, Sort(ref s) if s == "PROP");

    // A transported theorem's proof is recorded the same opaque way an
    // ordinary checked theorem's is; only a transported `fun`/`global`
    // becomes a delta and grows `lifted_names`, so later transports of
    // proofs calling `old_name` pick up `new_name` instead.
    if is_theorem {
        environment.add_to_context(new_name, new_type);
        environment.add_theorem_proof(new_name, &transported);
    } else {
        environment.add_substitution_with_type(
            new_name,
            &transported,
            new_type,
        );
        if let Some(config_mut) = environment.get_equivalence_mut(equiv_name)
        {
            config_mut
                .lifted_names
                .insert(old_name.to_string(), new_name.to_string());
        }
    }

    Ok(())
}
//
//
pub fn evaluate_inductive(
    environment: &mut Environment<Cic>,
    name: &str,
    params: &Vec<(String, CicTerm)>,
    ariety: &CicTerm,
    constructors: &Vec<(String, CicTerm)>,
) -> Result<(), LofError> {
    let ind_type = make_multiarg_fun_type(params, ariety);
    let ind_type = index_variables(&ind_type);
    environment.add_to_context(name, &ind_type);

    let mut constr_set = vec![];
    for (constr_name, constr_type) in constructors {
        let constr_type = make_multiarg_fun_type(&params, constr_type);
        let constr_type = index_variables(&constr_type);
        environment.add_to_context(constr_name, &constr_type);
        constr_set.push((constr_name.to_string(), constr_type));
    }

    environment.add_to_context(
        &format!("e_{}", name),
        &inductive_eliminator(
            name.to_string(),
            params.to_owned(),
            ariety.to_owned(),
            constructors.to_owned(),
        ),
    );
    environment.add_to_inductive_store(name, constr_set, params.len());

    Ok(())
}
//########################### STATEMENTS EXECUTION
//
//########################### HELPER FUNCTIONS
/// Given a `term` and a `pattern`, returns `true` if the term matches the
/// pattern, `false` otherwise
fn matches_pattern(term: &CicTerm, pattern: &CicTerm) -> bool {
    let used = get_applied_function(term);
    let constructor = get_applied_function(pattern);
    let actual_args = application_args(term);
    let formal_args = application_args(pattern);

    // TODO i think this should match the types as well but im not sure
    return (used == constructor) && (actual_args.len() == formal_args.len());
}

/// Given the matched `term` and the `pattern`, substitutes every pattern
/// variable the corresponding expression from `term` inside `body`
fn substitute_pattern_variables(
    term: &CicTerm,
    pattern: &CicTerm,
    body: &CicTerm,
) -> CicTerm {
    let actual_args = application_args(term);
    let formal_args = application_args(pattern);

    formal_args.iter().zip(actual_args.iter()).fold(
        body.clone(),
        |bound_body, (formal_arg, actual_arg)| {
            substitute_pattern_arg(formal_arg, actual_arg, &bound_body)
        },
    )
}

/// Substitutes a single `formal_arg` from a pattern with the corresponding `actual_arg`
fn substitute_pattern_arg(
    formal_arg: &CicTerm,
    actual_arg: &CicTerm,
    body: &CicTerm,
) -> CicTerm {
    match formal_arg {
        Variable(var_name, _) => substitute(body, var_name, actual_arg),
        Application(_, _) => {
            substitute_pattern_variables(actual_arg, formal_arg, body)
        }
        // metavariables (`?`) and other patterns bind nothing
        _ => body.clone(),
    }
}
//########################### HELPER FUNCTIONS

#[cfg(test)]
#[path = "../../tests/type_theory/cic/evaluation.rs"]
mod tests;
