use crate::type_theory::{
    cic::{
        cic::{
            Cic,
            CicTerm::{
                Abstraction, Application, Let, Product, Sort, Variable,
            },
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
fn test_let_reduction() {
    let mut test_env = Cic::default_environment();
    let zero = Variable("z".to_string(), GLOBAL_INDEX);
    test_env.add_to_context("Nat", &Sort("TYPE".to_string()));

    assert_eq!(
        one_step_reduction(
            &mut test_env,
            &Let(
                "n".to_string(),
                Box::new(None),
                Box::new(zero.clone()),
                Box::new(Variable("n".to_string(), 0)),
            ),
        ),
        zero.to_owned(),
        "Let definition doesnt reduce to its scope with substituted variable"
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

#[test]
fn test_match_reduction_binds_pattern_variables() {
    let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
    let succ = Variable("s".to_string(), GLOBAL_INDEX);
    let zero = Variable("z".to_string(), GLOBAL_INDEX);
    let mut test_env = Cic::default_environment();
    // pattern `s(n)` whose body just returns the bound variable `n`
    let succ_pattern = Application(
        Box::new(succ.clone()),
        Box::new(Variable("n".to_string(), GLOBAL_INDEX)),
    );
    let body_returning_bound_var = Variable("n".to_string(), GLOBAL_INDEX);

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

    assert_eq!(
        reduce_match(
            &mut test_env,
            &Application(Box::new(succ), Box::new(zero.clone())),
            &vec![(zero.clone(), zero.clone()), (
                succ_pattern,
                body_returning_bound_var
            )]
        ),
        zero,
        "Match reduction doesnt substitute the constructor argument for the pattern's bound variable in the branch body"
    );
}
