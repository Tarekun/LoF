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
fn try_iota_reduction(
    environment: &Environment<Cic>,
    term: &CicTerm,
) -> Option<CicTerm> {
    let elim_name = match get_applied_function(term) {
        Variable(name, NameKind::Const()) if name.starts_with("e_") => {
            name.to_owned()
        }
        _ => return None,
    };
    let type_name = elim_name.strip_prefix("e_")?.to_string();
    let param_count = environment.get_inductive_param_count(&type_name)?;
    let constructors = environment.get_constructor_signatures(&type_name)?;
    let constructor_count = constructors.len();
    let args = application_args(term);
    // #params + motive + #cases + instance
    let fixed_args = param_count + 1 + constructor_count + 1;

    // partial application nothing to compute
    if args.len() < fixed_args {
        return None;
    }

    let instance = args.last()?;
    let instance_head = get_applied_function(instance);
    let constructor_name = match &instance_head {
        Variable(name, NameKind::Const()) => name.to_owned(),
        // note: in case the instance isnt a constructor application
        // recursion is fully stuck and have nothing to reduce
        _ => return None,
    };
    let instance_args = application_args(instance);
    if instance_args.len() < param_count {
        return None;
    }

    let constructor_index = constructors
        .iter()
        .position(|(name, _)| name == &constructor_name)?;
    let constructor_type = constructors[constructor_index].1.to_owned();

    let case = args[param_count + 1 + constructor_index].to_owned();
    // params + motive + every case
    let leading_args = args[..param_count + 1 + constructor_count].to_vec();
    let own_args = &instance_args[param_count..];

    // collect the types of own_args, reducing the type of the constructor
    // by the instance arguments (mainly for left params instantiation)
    let mut own_arg_types = vec![];
    let mut remaining_type = constructor_type;
    for supplied in instance_args.iter() {
        match remaining_type {
            Product(binder, domain, codomain) => {
                own_arg_types.push((*domain).to_owned());
                remaining_type = substitute(&codomain, &binder, supplied);
            }
            // fewer Pi layers than supplied arguments: not a shape this
            // rule understands
            _ => return None,
        }
    }
    let own_arg_types = &own_arg_types[param_count..];

    let mut reduced = case;
    for (own_arg, own_arg_type) in own_args.iter().zip(own_arg_types.iter()) {
        reduced = Application(Box::new(reduced), Box::new(own_arg.to_owned()));

        // in case own_arg_type is this inductive type add an inductive hypothesis
        if is_instance_of(own_arg_type, &type_name) {
            // this occurrence's own indices, ie whatever `Type(params.., i..)`
            // it is an instance of, minus the (uniform) parameters
            let occurrence_args = application_args(own_arg_type);
            if occurrence_args.len() < param_count {
                return None;
            }
            let occurrence_indices = &occurrence_args[param_count..];

            let mut hypothesis_args = leading_args.clone();
            hypothesis_args.extend(occurrence_indices.iter().cloned());
            hypothesis_args.push(own_arg.to_owned());
            let inductive_hypothesis = apply_arguments(
                &Variable(elim_name.to_owned(), NameKind::Const()),
                hypothesis_args,
            );
            reduced =
                Application(Box::new(reduced), Box::new(inductive_hypothesis));
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
    }
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
