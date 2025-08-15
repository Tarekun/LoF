use core::panic;

use super::cic::CicStm::{Axiom, Fun, Let, Theorem};
use super::cic::CicTerm::{Abstraction, Application, Match, Product, Variable};
use super::cic::{Cic, CicStm, CicTerm};
use super::cic_utils::{eta_expand, make_multiarg_fun_type, substitute};
use crate::misc::Union;
use crate::parser::api::Tactic;
use crate::type_theory::cic::cic_utils::{
    application_args, get_applied_function,
};
use crate::type_theory::cic::type_check_inductive::inductive_eliminator;
use crate::type_theory::commons::evaluation::{
    generic_evaluate_axiom, generic_evaluate_let, generic_evaluate_theorem,
    generic_reduce_variable,
};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::Kernel;
use crate::type_theory::interface::Reducer;

//########################### TERM βδ-REDUCTION
pub fn one_step_reduction(
    environment: &mut Environment<Cic>,
    term: &CicTerm,
) -> CicTerm {
    match term {
        Variable(var_name, _) => reduce_variable(environment, var_name, term),
        Application(left, right) => {
            reduce_application(environment, left, right)
        }
        Match(matched_term, branches) => {
            reduce_match(environment, matched_term, branches)
        }
        _ => term.clone(),
    }
}
//
//
fn reduce_variable(
    environment: &Environment<Cic>,
    var_name: &str,
    og_term: &CicTerm,
) -> CicTerm {
    generic_reduce_variable::<Cic>(environment, var_name, og_term)
}
//
/// Given a functional term returns its body if it has one defined, or None if
/// it doesnt exist. Assumes that function variables are already β-reduced
fn get_body(reduced_function: &CicTerm) -> Option<CicTerm> {
    match reduced_function {
        Abstraction(_, _, body) => Some(*body.clone()),
        _ => None,
    }
}
fn reduce_application(
    environment: &mut Environment<Cic>,
    left: &CicTerm,
    right: &CicTerm,
) -> CicTerm {
    match Cic::type_check_term(&left, environment) {
        Ok(fun_type) => match fun_type {
            Product(var_name, _, _) => {
                // if left is function variable take its body, otherwise gets left back
                let left_reduced = Cic::normalize_term(environment, left);
                // TODO do i substitute right or do i substitute its reduction? big deal
                let right_reduced = Cic::normalize_term(environment, right);

                match get_body(&left_reduced) {
                    Some(body) => substitute(&body, &var_name, &right_reduced),
                    None => Application(
                        Box::new(left_reduced),
                        Box::new(right_reduced),
                    ),
                }
            }
            _ => {
                panic!(
                    "Trying to reduce an application of term {:?} that doesn't have a functional type. This should have been caught sooner", 
                    left
                );
            }
        },
        Err(message) => {
            panic!(
                "Trying to reduce an application of term {:?} that is ill-typed. This should have been caught sooner. Details {:?}",
                left, message
            );
        }
    }
}
//
//
fn reduce_match(
    environment: &mut Environment<Cic>,
    matched_term: &CicTerm,
    branches: &Vec<(CicTerm, CicTerm)>,
) -> CicTerm {
    let normalized_term = Cic::normalize_term(environment, matched_term);
    for (pattern, body) in branches {
        if matches_pattern(&normalized_term, pattern) {
            return body.clone();
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
) -> () {
    match stm {
        Axiom(axiom_name, formula) => {
            evaluate_axiom(environment, axiom_name, formula)
        }
        Let(var_name, var_type, body) => {
            evaluate_let(environment, var_name, var_type, body)
        }
        Fun(fun_name, args, out_type, body, is_rec) => {
            evaluate_fun(environment, fun_name, args, out_type, body, is_rec)
        }
        Theorem(theorem_name, formula, proof) => {
            evaluate_theorem(environment, theorem_name, formula, proof)
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
pub fn evaluate_axiom(
    environment: &mut Environment<Cic>,
    axiom_name: &str,
    formula: &CicTerm,
) -> () {
    generic_evaluate_axiom::<Cic>(environment, axiom_name, formula);
}
//
//
pub fn evaluate_let(
    environment: &mut Environment<Cic>,
    var_name: &str,
    var_type: &Option<CicTerm>,
    body: &CicTerm,
) -> () {
    generic_evaluate_let::<Cic>(environment, var_name, var_type, body);
}
//
//
pub fn evaluate_fun(
    environment: &mut Environment<Cic>,
    fun_name: &str,
    args: &Vec<(String, CicTerm)>,
    out_type: &CicTerm,
    body: &CicTerm,
    _is_rec: &bool,
) -> () {
    let fun_type = make_multiarg_fun_type(args, out_type);
    let full_body = eta_expand(args, body);
    environment.add_substitution_with_type(fun_name, &full_body, &fun_type);
    // generic_evaluate_fun::<Cic, _>(
    //     environment,
    //     fun_name,
    //     args,
    //     out_type,
    //     body,
    //     is_rec,
    //     make_multiarg_fun_type,
    // );
}
//
//
pub fn evaluate_theorem(
    environment: &mut Environment<Cic>,
    theorem_name: &str,
    formula: &CicTerm,
    proof: &Union<CicTerm, Vec<Tactic<CicTerm>>>,
) -> () {
    generic_evaluate_theorem::<Cic, CicTerm>(
        environment,
        theorem_name,
        formula,
        proof,
    );
}
//
//
pub fn evaluate_inductive(
    environment: &mut Environment<Cic>,
    name: &str,
    params: &Vec<(String, CicTerm)>,
    ariety: &CicTerm,
    constructors: &Vec<(String, CicTerm)>,
) {
    //TODO make a record of the full constructor list for match type checking
    let ind_type = make_multiarg_fun_type(params, ariety);
    environment.add_to_context(name, &ind_type);
    for (constr_name, constr_type) in constructors {
        let constr_type = make_multiarg_fun_type(&params, constr_type);
        environment.add_to_context(constr_name, &constr_type);
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
//########################### HELPER FUNCTIONS

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::type_theory::{
        cic::{
            cic::{
                Cic,
                CicTerm::{Abstraction, Application, Product, Sort, Variable},
                GLOBAL_INDEX,
            },
            evaluation::{
                matches_pattern, reduce_application, reduce_match,
                reduce_variable,
            },
        },
        interface::TypeTheory,
    };

    #[test]
    fn test_check_pattern_matching() {
        let zero = Variable("z".to_string(), GLOBAL_INDEX);
        let succ = Variable("s".to_string(), GLOBAL_INDEX);

        assert!(
            matches_pattern(&zero, &zero),
            "Pattern matching refutes identical constants"
        );
        assert!(
            !matches_pattern(&zero, &succ),
            "Pattern matching accepts different constants"
        );
        assert!(
            matches_pattern(
                &Application(Box::new(succ.clone()), Box::new(zero.clone())),
                &Application(
                    Box::new(succ.clone()),
                    Box::new(Variable("renamed_argument".to_string(), 0)),
                )
            ),
            "Pattern matching refutes application with renamed argument"
        );
        assert!(
            !matches_pattern(
                &Application(
                    Box::new(Application(
                        Box::new(Variable("cons".to_string(), GLOBAL_INDEX)),
                        Box::new(zero.clone()),
                    )),
                    Box::new(Variable("l".to_string(), GLOBAL_INDEX))
                ),
                &Application(
                    Box::new(Variable("cons".to_string(), GLOBAL_INDEX)),
                    Box::new(zero),
                )
            ),
            "Pattern matching accepts only partial pattern"
        );
    }

    #[test]
    fn test_var_reduction() {
        let mut test_env = Cic::default_environment();
        test_env.add_substitution_with_type(
            "test",
            &Variable("Unit".to_string(), GLOBAL_INDEX),
            &Sort("TYPE".to_string()),
        );

        assert_eq!(
            reduce_variable(
                &test_env,
                "constant",
                &Variable("constant".to_string(), GLOBAL_INDEX),
            ),
            Variable("constant".to_string(), GLOBAL_INDEX),
            "Constant δ-reduces to something other than itself"
        );
        assert_eq!(
            reduce_variable(
                &test_env,
                "test",
                &Variable("test".to_string(), 0)
            ),
            Variable("Unit".to_string(), GLOBAL_INDEX),
            "Defined variable doesnt δ-reduce to its body"
        );
    }

    #[test]
    fn test_app_reduction() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let succ = Variable("s".to_string(), GLOBAL_INDEX);
        let zero = Variable("z".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();
        test_env.add_to_context("Nat", &Sort("TYPE".to_string()));
        test_env.add_to_context("z", &nat);
        test_env.add_to_context(
            "s",
            &Product(
                "".to_string(),
                Box::new(nat.clone()),
                Box::new(nat.clone()),
            ),
        );
        test_env.add_substitution_with_type(
            "add_one",
            &Abstraction(
                "n".to_string(),
                Box::new(nat.clone()),
                Box::new(Application(
                    Box::new(succ.clone()),
                    Box::new(Variable("n".to_string(), 0)),
                )),
            ),
            &Product(
                "n".to_string(),
                Box::new(nat.clone()),
                Box::new(nat.clone()),
            ),
        );

        assert_eq!(
            reduce_application(&mut test_env, &succ.clone(), &zero),
            Application(Box::new(succ.clone()), Box::new(zero)),
            "Function application of normal form returns a different term"
        );
        assert_eq!(
            reduce_application(
                &mut test_env,
                &Variable("add_one".to_string(), GLOBAL_INDEX),
                &Variable("arg".to_string(), GLOBAL_INDEX)
            ),
            Application(
                Box::new(succ.clone()),
                Box::new(Variable("arg".to_string(), GLOBAL_INDEX)),
            ),
            "Function application doesnt reduce to the function body with substituted variable"
        );
    }

    #[test]
    fn test_match_reduction() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let succ = Variable("s".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();
        let zero = Variable("z".to_string(), GLOBAL_INDEX);
        let succ_pattern = Application(
            Box::new(succ.clone()),
            Box::new(Variable("n".to_string(), 0)),
        );
        let true_term = Variable("true".to_string(), GLOBAL_INDEX);
        let false_term = Variable("false".to_string(), GLOBAL_INDEX);

        test_env.add_to_context("Nat", &Sort("TYPE".to_string()));
        test_env.add_to_context("z", &nat.clone());
        test_env.add_to_context(
            "s",
            &Product(
                "_".to_string(),
                Box::new(nat.clone()),
                Box::new(nat.clone()),
            ),
        );
        test_env.add_substitution_with_type("x", &zero, &nat.clone());

        assert_eq!(
            reduce_match(
                &mut test_env,
                &zero,
                &vec![
                    (zero.clone(), true_term.clone()),
                    (succ_pattern.clone(), false_term.clone())
                ]
            ),
            true_term,
            "Match term doesnt δ-reduce to the right branch body"
        );
        assert_eq!(
            reduce_match(
                &mut test_env,
                &Variable("x".to_string(), 0),
                &vec![
                    (zero.clone(), true_term.clone()),
                    (succ_pattern.clone(), false_term.clone())
                ]
            ),
            true_term,
            "Match term doesnt δ-reduce if matching a variable that needs reduction"
        );
        assert_eq!(
            reduce_match(
                &mut test_env,
                &Application(
                    Box::new(succ),
                    Box::new(Variable("z".to_string(), GLOBAL_INDEX))
                ),
                &vec![
                    (zero.clone(), true_term.clone()),
                    (succ_pattern.clone(), false_term.clone())
                ]
            ),
            false_term,
            "Match term doesnt δ-reduce if matching an application pattern"
        );
    }
}
