use super::cic::CicStm::{Axiom, Fun, Global, Theorem};
use super::cic::CicTerm::{
    Abstraction, Application, Let, Match, Product, Variable,
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
use crate::type_theory::interface::Reducer;

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

    let (constructor_name, instance_args) = split_instance(args.last()?)?;
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
    let normalized_term = Cic::normalize_term(environment, matched_term);
    for (pattern, body) in branches {
        if matches_pattern(&normalized_term, pattern) {
            return substitute_pattern_variables(
                &normalized_term,
                pattern,
                body,
            );
        }
    }

    // fallback in case normalized_term is a free variable with no reduction
    // to any constructor call
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
