use crate::type_theory::{
    interface::{Kernel, TypeTheory},
    sup::sup::{
        Sup,
        SupFormula::{Atom, Clause, Equality, ForAll, Not},
        SupTerm::{Application, Variable},
    },
};

mod variable {
    use super::*;

    #[test]
    fn test_variable_type_check() {
        let nat = Atom("Nat".to_string(), vec![]);
        let mut test_env = Sup::default_environment();
        test_env.add_to_context("n", &nat);

        assert_eq!(
            Sup::type_check_term(&Variable("n".to_string()), &mut test_env),
            Ok(nat.clone()),
            "Variable type checking isnt working properly"
        );
        assert!(
            Sup::type_check_term(
                &Variable("stupid_unbound_variable".to_string()),
                &mut test_env,
            )
            .is_err(),
            "Variable type checking is accepting an unbound variable"
        );
    }
}

mod application {
    use super::*;

    #[test]
    fn test_application_type_check() {
        let nat = Atom("Nat".to_string(), vec![]);
        let mut test_env = Sup::default_environment();
        test_env.add_to_context(
            "f",
            &ForAll(
                "_".to_string(),
                Box::new(nat.clone()),
                Box::new(nat.clone()),
            ),
        );
        test_env.add_to_context("n", &nat);

        assert_eq!(
            Sup::type_check_term(
                &Application(
                    "f".to_string(),
                    vec![Variable("n".to_string())]
                ),
                &mut test_env,
            ),
            Ok(nat.clone()),
            "Application type checker doesnt work properly"
        );
        assert!(
            Sup::type_check_term(
                &Application(
                    "stupid_unbound_fun".to_string(),
                    vec![Variable("n".to_string())]
                ),
                &mut test_env,
            )
            .is_err(),
            "Application type checking accepts an unbound function"
        );
        assert!(
            Sup::type_check_term(
                &Application("f".to_string(), vec![]),
                &mut test_env,
            )
            .is_err(),
            "Application type checking accepts a call with the wrong number of arguments"
        );
        assert!(
            Sup::type_check_term(
                &Application(
                    "f".to_string(),
                    vec![Variable("stupid_unbound_arg".to_string())]
                ),
                &mut test_env,
            )
            .is_err(),
            "Application type checking accepts an unbound argument"
        );
    }
}

mod atomic {
    use super::*;

    #[test]
    fn test_atomic_type_check() {
        let nat = Atom("Nat".to_string(), vec![]);
        let mut test_env = Sup::default_environment();
        test_env.add_to_context(
            "p",
            &ForAll(
                "_".to_string(),
                Box::new(nat.clone()),
                Box::new(nat.clone()),
            ),
        );
        test_env.add_to_context("n", &nat);

        assert_eq!(
            Sup::type_check_type(
                &Atom("p".to_string(), vec![Variable("n".to_string())]),
                &mut test_env,
            ),
            Ok(Atom("p".to_string(), vec![Variable("n".to_string())])),
            "Atomic formula type checker doesnt work properly"
        );
        assert!(
            Sup::type_check_type(
                &Atom(
                    "stupid_unbound_predicate".to_string(),
                    vec![Variable("n".to_string())]
                ),
                &mut test_env,
            )
            .is_err(),
            "Atomic formula type checker accepts an unbound predicate"
        );
        assert!(
            Sup::type_check_type(
                &Atom(
                    "p".to_string(),
                    vec![Variable("stupid_unbound_arg".to_string())]
                ),
                &mut test_env,
            )
            .is_err(),
            "Atomic formula type checker accepts an unbound argument"
        );
    }
}

mod equality {
    use super::*;

    #[test]
    fn test_equality_type_check() {
        let n = Variable("n".to_string());
        let mut test_env = Sup::default_environment();

        assert_eq!(
            Sup::type_check_type(&Equality(n.clone(), n.clone()), &mut test_env),
            Ok(Equality(n.clone(), n.clone())),
            "Equality type checker refuses a term equated with itself"
        );
        // NOTE: `type_check_equality` currently delegates to
        // `Sup::base_term_equality`, which requires the two sides to be
        // syntactically identical. This means a perfectly well-formed
        // equality between two *different* (but same-sorted) terms, e.g.
        // `n = m`, is rejected here. That looks like a bug rather than
        // intended behavior (an equality atom should type check regardless
        // of whether the two sides are provably equal), but the fix depends
        // on the intended semantics, so this test pins down the current
        // behavior rather than asserting what it "should" do.
        assert!(
            Sup::type_check_type(
                &Equality(
                    Variable("n".to_string()),
                    Variable("m".to_string())
                ),
                &mut test_env,
            )
            .is_err(),
            "Equality type checker's current implementation rejects equalities between distinct terms"
        );
    }
}

mod not {
    use super::*;

    #[test]
    fn test_not_type_check() {
        let nat = Atom("Nat".to_string(), vec![]);
        let mut test_env = Sup::default_environment();
        // 0-arity predicates are still looked up via the variable context,
        // so the sort marker itself needs to be declared
        test_env.add_to_context("Nat", &nat);

        assert_eq!(
            Sup::type_check_type(&Not(Box::new(nat.clone())), &mut test_env),
            Ok(Not(Box::new(nat.clone()))),
            "Not type checker doesnt work properly"
        );
        assert!(
            Sup::type_check_type(
                &Not(Box::new(Atom(
                    "stupid_unbound_predicate".to_string(),
                    vec![]
                ))),
                &mut test_env,
            )
            .is_err(),
            "Not type checker accepts negation of an unbound predicate"
        );
    }
}

mod forall {
    use super::*;

    #[test]
    fn test_forall_type_check() {
        let nat = Atom("Nat".to_string(), vec![]);
        let mut test_env = Sup::default_environment();
        // 0-arity predicates are still looked up via the variable context,
        // so the sort marker itself needs to be declared
        test_env.add_to_context("Nat", &nat);
        test_env.add_to_context(
            "p",
            &ForAll(
                "_".to_string(),
                Box::new(nat.clone()),
                Box::new(nat.clone()),
            ),
        );

        assert!(
            Sup::type_check_type(
                &ForAll(
                    "x".to_string(),
                    Box::new(nat.clone()),
                    Box::new(Atom(
                        "p".to_string(),
                        vec![Variable("x".to_string())]
                    )),
                ),
                &mut test_env,
            )
            .is_ok(),
            "Forall type checker doesnt work properly"
        );
        assert!(
            Sup::type_check_type(
                &ForAll(
                    "x".to_string(),
                    Box::new(Atom(
                        "StupidUnboundSort".to_string(),
                        vec![]
                    )),
                    Box::new(nat.clone()),
                ),
                &mut test_env,
            )
            .is_err(),
            "Forall type checker accepts a quantifier over an unbound sort"
        );
        assert!(
            Sup::type_check_type(
                &ForAll(
                    "x".to_string(),
                    Box::new(nat.clone()),
                    Box::new(Atom(
                        "stupid_unbound_predicate".to_string(),
                        vec![Variable("x".to_string())]
                    )),
                ),
                &mut test_env,
            )
            .is_err(),
            "Forall type checker accepts a body that doesnt type check"
        );
    }
}

mod clause {
    use super::*;

    #[test]
    fn test_clause_type_check() {
        let mut test_env = Sup::default_environment();
        test_env.add_to_context(
            "p",
            &ForAll(
                "_".to_string(),
                Box::new(Atom("Nat".to_string(), vec![])),
                Box::new(Atom("Nat".to_string(), vec![])),
            ),
        );
        test_env.add_to_context("n", &Atom("Nat".to_string(), vec![]));

        let literal = Atom("p".to_string(), vec![Variable("n".to_string())]);
        let negated_literal = Not(Box::new(literal.clone()));

        assert!(
            Sup::type_check_type(
                &Clause(vec![literal.clone(), negated_literal.clone()]),
                &mut test_env,
            )
            .is_ok(),
            "Clause type checker refuses a clause made of well typed literals"
        );
        assert!(
            Sup::type_check_type(&Clause(vec![]), &mut test_env).is_ok(),
            "Clause type checker refuses the empty clause"
        );
        assert!(
            Sup::type_check_type(
                &Clause(vec![Not(Box::new(negated_literal))]),
                &mut test_env,
            )
            .is_err(),
            "Clause type checker accepts a doubly negated literal, which isnt a literal"
        );
        assert!(
            Sup::type_check_type(
                &Clause(vec![Atom(
                    "stupid_unbound_predicate".to_string(),
                    vec![]
                )]),
                &mut test_env,
            )
            .is_err(),
            "Clause type checker accepts a clause with an ill typed literal"
        );
    }
}
