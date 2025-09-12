use super::cic::CicStm::{Axiom, Fun, Let, Theorem};
use super::cic::CicTerm::{Abstraction, Application, Match, Variable};
use super::cic::{Cic, CicStm, CicTerm};
use super::cic_utils::make_multiarg_fun_type;
use crate::type_theory::cic::cic_utils::{
    application_args, get_applied_function,
};
use crate::type_theory::cic::type_check_inductive::inductive_eliminator;
use crate::type_theory::commons::evaluation::{
    evaluate_axiom, evaluate_fun, evaluate_let, evaluate_theorem,
    reduce_application, reduce_variable,
};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::Reducer;
use core::panic;

//########################### TERM βδ-REDUCTION
pub fn one_step_reduction(
    environment: &mut Environment<Cic>,
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
        Match(matched_term, branches) => {
            reduce_match(environment, matched_term, branches)
        }
        _ => term.clone(),
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
            evaluate_axiom::<Cic>(environment, axiom_name, formula)
        }
        Let(var_name, var_type, body) => {
            evaluate_let::<Cic>(environment, var_name, var_type, body)
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
            );
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
                matches_pattern, one_step_reduction, reduce_match,
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
            one_step_reduction(
                &mut test_env,
                &Application(Box::new(succ.clone()), Box::new(zero.clone()))
            ),
            Application(Box::new(succ.clone()), Box::new(zero)),
            "Function application of normal form returns a different term"
        );
        assert_eq!(
            one_step_reduction(
                &mut test_env,
                &Application(
                    Box::new(Variable("add_one".to_string(), GLOBAL_INDEX)),
                    Box::new(Variable("arg".to_string(), GLOBAL_INDEX))
                )
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
