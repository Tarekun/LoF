use super::cic::CicStm::{Axiom, Fun, Global, Theorem};
use super::cic::CicTerm::{Abstraction, Application, Let, Match, Variable};
use super::cic::{Cic, CicStm, CicTerm};
use super::cic_utils::make_multiarg_fun_type;
use crate::error::LofError;
use crate::type_theory::cic::cic_utils::{
    application_args, get_applied_function, index_variables, substitute,
};
use crate::type_theory::cic::type_check::inductive_eliminator;
use crate::type_theory::commons::evaluation::{
    evaluate_axiom, evaluate_fun, evaluate_global, evaluate_theorem,
    reduce_application, reduce_let, reduce_variable,
};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::Reducer;
use core::panic;

//########################### TERM βδ-REDUCTION
pub fn one_step_reduction(
    environment: &Environment<Cic>,
    term: &CicTerm,
) -> CicTerm {
    match term {
        Variable(var_name, _) => {
            reduce_variable::<Cic>(environment, var_name, term)
        }
        Application(left, right) => reduce_application::<Cic, _, _>(
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
                Application(Box::new(left_reduced), Box::new(right_reduced))
            },
        ),
        Let(var_name, var_type, body, scope) => {
            reduce_let(environment, var_name, var_type, body, scope)
        }
        Match(matched_term, branches) => {
            reduce_match(environment, matched_term, branches)
        }
        _ => term.clone(),
    }
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

    panic!(
        "No pattern matched the term {:?}, if this is a type checking or exhaustiveness error, it should have been caught sooner",
        matched_term
    );
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
    let ind_type = index_variables(&make_multiarg_fun_type(params, ariety));
    environment.add_to_context(name, &ind_type);

    let mut constr_set = vec![];
    for (constr_name, constr_type) in constructors {
        // `constr_type` was elaborated on its own (see `elaborate_inductive`),
        // before `params` existed as enclosing binders, so any reference to
        // a type parameter inside it (eg. `P`/`Q` in `left: P -> Or(P, Q)`)
        // was elaborated as an unbound/global variable. Wrapping it in the
        // parameters' Products here makes it a bound variable in truth, but
        // doesn't retag those existing occurrences - left unfixed, they stay
        // marked as global constants, which makes the constructor's type
        // impossible to unify against a concrete instantiation (as `apply`
        // needs to): unification treats a global-tagged variable as a fixed
        // constant rather than something it can solve for.
        let constr_type =
            index_variables(&make_multiarg_fun_type(&params, constr_type));
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
    environment.add_constructor_store(name, constr_set);

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

