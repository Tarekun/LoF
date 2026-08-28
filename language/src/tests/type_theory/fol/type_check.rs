use crate::type_theory::{
    environment::Environment,
    fol::fol::{
        Fol,
        FolFormula::{self, Arrow, ForAll, Predicate},
        FolStm::{Axiom, Fun, Global},
        FolTerm::{Abstraction, Application, Let, Variable},
    },
    interface::{Kernel, TypeTheory},
};

mod variable {
    use super::*;

    #[test]
    fn test_var_type_check() {
        let mut test_env = Fol::default_environment();
        test_env.add_to_context("it", &Predicate("Unit".to_string(), vec![]));

        assert_eq!(
            Fol::type_check_term(&Variable("it".to_string()), &mut test_env),
            Ok(Predicate("Unit".to_string(), vec![])),
            "Variable type checking isnt working properly"
        );
        assert!(
            Fol::type_check_term(
                &Variable("stupid_unbound_variable".to_string()),
                &mut test_env,
            )
            .is_err(),
            "Variable type checking is accepting unbound variable"
        );
        assert!(
            Fol::type_check_term(&Variable("it".to_string()), &mut test_env,)
                .is_ok(),
            "Top level type checker doesnt support variables"
        );
    }
}

mod abstraction {
    use super::*;

    #[test]
    fn test_abs_type_check() {
        let mut test_env = Fol::default_environment();
        let unit = Predicate("Unit".to_string(), vec![]);

        assert_eq!(
            Fol::type_check_term(
                &Abstraction(
                    "x".to_string(),
                    Box::new(unit.clone()),
                    Box::new(Variable("x".to_string()))
                ),
                &mut test_env,
            ),
            Ok(Arrow(Box::new(unit.clone()), Box::new(unit.clone()))),
            "Abstraction type checker doesnt work properly"
        );
        assert!(
            Fol::type_check_term(
                &Abstraction(
                    "x".to_string(),
                    Box::new(unit.clone()),
                    Box::new(Variable("x".to_string())),
                ),
                &mut test_env,
            )
            .is_ok(),
            "Top level type checking doesnt support abstraction"
        );

        assert!(
            Fol::type_check_term(
                &Abstraction(
                    "x".to_string(),
                    Box::new(Predicate(
                        "StupidUnboundType".to_string(),
                        vec![]
                    )),
                    Box::new(Variable("x".to_string()))
                ),
                &mut test_env,
            )
            .is_err(),
            "Abstraction type checker accepts argument over undefined type"
        );
        assert!(
            Fol::type_check_term(
                &Abstraction(
                    "x".to_string(),
                    Box::new(Predicate(
                        "StupidUnboundType".to_string(),
                        vec![]
                    )),
                    Box::new(Variable("stupid_unbound_variable".to_string()))
                ),
                &mut test_env,
            )
            .is_err(),
            "Abstraction type checker accepts argument over ill typed body"
        );
    }
}

mod application {
    use super::*;

    #[test]
    fn test_app_type_check() {
        let unit = Predicate("Unit".to_string(), vec![]);
        let nat = Predicate("Nat".to_string(), vec![]);
        let mut test_env: Environment<Fol> = Environment::with_defaults(
            vec![],
            vec![],
            vec![("Nat", &vec![]), ("Unit", &vec![])],
        );
        test_env.add_to_context(
            "f",
            &Arrow(Box::new(nat.clone()), Box::new(nat.clone())),
        );
        test_env.add_to_context("x", &nat.clone());
        test_env.add_to_context("it", &unit.clone());

        assert_eq!(
            Fol::type_check_term(
                &Application(
                    Box::new(Variable("f".to_string())),
                    Box::new(Variable("x".to_string())),
                ),
                &mut test_env,
            ),
            Ok(nat.clone()),
            "Application type checker doesnt work properly"
        );
        assert!(
            Fol::type_check_term(
                &Application(
                    Box::new(Variable("f".to_string())),
                    Box::new(Variable("x".to_string()))
                ),
                &mut test_env,
            )
            .is_ok(),
            "Top level type checking doesnt support application"
        );

        assert!(
            Fol::type_check_term(
                &Application(
                    Box::new(Variable("stupid_unbound_fun".to_string())),
                    Box::new(Variable("x".to_string())),
                ),
                &mut test_env,
            )
            .is_err(),
            "Application type checking accepts unbound function"
        );
        assert!(
            Fol::type_check_term(
                &Application(
                    Box::new(Variable("f".to_string())),
                    Box::new(Variable("stupid_unbound_arg".to_string())),
                ),
                &mut test_env,
            )
            .is_err(),
            "Application type checking accepts unbound argument"
        );
        assert!(
            Fol::type_check_term(
                &Application(
                    Box::new(Variable("f".to_string())),
                    Box::new(Variable("it".to_string())),
                ),
                &mut test_env,
            )
            .is_err(),
            "Application type checking accepts application with incompatible types"
        );
    }
}

mod sort {
    use super::*;

    #[test]
    fn test_sort_type_check() {
        let unit = Predicate("Unit".to_string(), vec![]);
        let mut test_env: Environment<Fol> =
            Environment::with_defaults(vec![], vec![], vec![("Unit", &vec![])]);

        assert!(
            Fol::type_check_type(&unit.clone(), &mut test_env).is_ok(),
            "Predicate-type type checking refutes bound type"
        );
        assert!(
            Fol::type_check_type(
                &Predicate("StupidUnboundType".to_string(), vec![]),
                &mut test_env
            )
            .is_err(),
            "Predicate-type type checking accepts unbound type"
        );
    }
}

mod arrow {
    use super::*;

    #[test]
    fn test_arrow_type_check() {
        let nat = Predicate("Nat".to_string(), vec![]);
        let mut test_env: Environment<Fol> =
            Environment::with_defaults(vec![], vec![], vec![("Nat", &vec![])]);

        assert!(
            Fol::type_check_type(
                &Arrow(Box::new(nat.clone()), Box::new(nat.clone())),
                &mut test_env
            )
            .is_ok(),
            "Arrow type checker refutes simple Nat->Nat"
        );
        assert!(
            Fol::type_check_type(
                &Arrow(
                    Box::new(Predicate(
                        "StupidUnboundType".to_string(),
                        vec![]
                    )),
                    Box::new(nat.clone())
                ),
                &mut test_env,
            )
            .is_err(),
            "Arrow type checker accepts unbound domain"
        );
        assert!(
            Fol::type_check_type(
                &Arrow(
                    Box::new(nat.clone()),
                    Box::new(Predicate(
                        "StupidUnboundType".to_string(),
                        vec![]
                    ))
                ),
                &mut test_env,
            )
            .is_err(),
            "Arrow type checker accepts unbound codomain"
        );
    }
}

mod forall {
    use super::*;

    #[test]
    fn test_forall_type_check() {
        let top: FolFormula = Predicate("Top".to_string(), vec![]);
        let nat = Predicate("Nat".to_string(), vec![]);
        let mut test_env: Environment<Fol> = Environment::with_defaults(
            vec![],
            vec![],
            vec![("Top", &vec![]), ("Nat", &vec![])],
        );

        assert!(
            Fol::type_check_type(
                &ForAll(
                    "x".to_string(),
                    Box::new(nat.clone()),
                    Box::new(top.clone())
                ),
                &mut test_env,
            )
            .is_ok(),
            "Forall type checker doesnt work properly"
        );
        assert!(
            Fol::type_check_type(
                &ForAll(
                    "x".to_string(),
                    Box::new(Predicate(
                        "StupidUnboundType".to_string(),
                        vec![]
                    )),
                    Box::new(top)
                ),
                &mut test_env,
            )
            .is_err(),
            "Forall type checker accepts forall dependent on unbound type"
        );
        assert!(
            Fol::type_check_type(
                &ForAll(
                    "x".to_string(),
                    Box::new(nat),
                    Box::new(Predicate(
                        "StupidUnboundType".to_string(),
                        vec![]
                    ))
                ),
                &mut test_env,
            )
            .is_err(),
            "Forall type checker accepts forall with ill typed body"
        );
    }
}

mod let_expr {
    use super::*;

    #[test]
    fn test_type_check_let() {
        let mut test_env = Fol::default_environment();
        let nat = Predicate("Nat".to_string(), vec![]);
        let zero = Variable("z".to_string());
        test_env.add_to_context("z", &nat);

        assert!(
            Fol::type_check_term(
                &Let(
                    "n".to_string(),
                    Box::new(Some(nat.clone())),
                    Box::new(zero.clone()),
                    Box::new(Variable("n".to_string())),
                ),
                &mut test_env
            )
            .is_ok(),
            "Type checker doesnt support let definitions"
        );
        assert!(
            Fol::type_check_term(
                &Let(
                    "n".to_string(),
                    Box::new(None),
                    Box::new(zero.clone()),
                    Box::new(Variable("n".to_string())),
                ),
                &mut test_env
            )
            .is_ok(),
            "Let type checker doesnt supported untyped definitions"
        );
        assert!(
            Fol::type_check_term(
                &Let(
                    "n".to_string(),
                    Box::new(Some(Predicate(
                        "UnboundType".to_string(),
                        vec![]
                    ))),
                    Box::new(zero.clone()),
                    Box::new(Variable("n".to_string())),
                ),
                &mut test_env
            )
            .is_err(),
            "Let type checker accepts definition with unbound annotated type"
        );
        assert!(
            Fol::type_check_term(
                &Let(
                    "n".to_string(),
                    Box::new(Some(nat.clone())),
                    Box::new(Variable("unbound_term".to_string())),
                    Box::new(Variable("n".to_string())),
                ),
                &mut test_env
            )
            .is_err(),
            "Let type checker accepts definition with ill-typed body"
        );
        assert!(
            Fol::type_check_term(
                &Let(
                    "n".to_string(),
                    Box::new(Some(nat.clone())),
                    Box::new(zero.clone()),
                    Box::new(Variable("unbound_term".to_string())),
                ),
                &mut test_env
            )
            .is_err(),
            "Let type checker accepts definition with ill-typed scope"
        );
    }
}

mod axiom {
    use super::*;

    #[test]
    fn test_axiom_type_check() {
        let top: FolFormula = Predicate("Top".to_string(), vec![]);
        let mut test_env: Environment<Fol> =
            Environment::with_defaults(vec![], vec![], vec![("Top", &vec![])]);
        let res = Fol::type_check_stm(
            &Axiom("test_axiom".to_string(), top.clone()),
            &mut test_env,
        );

        assert!(
            res.is_ok(),
            "Axiom type checker failed with error {:?}",
            res.err()
        );
        assert!(
            Fol::type_check_stm(
                &Axiom("other_name".to_string(), top.clone()),
                &mut test_env
            )
            .is_ok(),
            "Top level type checker doesnt support axioms",
        );
        assert_eq!(
            test_env.get_from_context("test_axiom"),
            Some(("test_axiom".to_string(), top)),
            "Axiom type checker did not update the context"
        );
    }
}

mod global {
    use super::*;

    #[test]
    fn test_global_type_check() {
        let nat = Predicate("Nat".to_string(), vec![]);
        let zero = Variable("zero".to_string());
        let mut test_env: Environment<Fol> = Environment::with_defaults(
            vec![("zero", &nat)],
            vec![],
            vec![("Nat", &vec![])],
        );

        let res = Fol::type_check_stm(
            &Global("n".to_string(), Some(nat.clone()), Box::new(zero.clone())),
            &mut test_env,
        );
        assert!(res.is_ok(), "Let type checker failed with {:?}", res.err());
        assert_eq!(
            test_env.get_from_deltas("n"),
            Some(("n".to_string(), zero.clone())),
            "Let type checker didnt update the context properly"
        );
        assert!(
            Fol::type_check_stm(
                &Global(
                    "m".to_string(),
                    Some(nat.clone()),
                    Box::new(zero.clone())
                ),
                &mut test_env
            )
            .is_ok(),
            "Top level type checker doesnt support let definitions"
        );
        assert!(
            Fol::type_check_stm(
                &Global("asd".to_string(), None, Box::new(zero.clone())),
                &mut test_env,
            )
            .is_ok(),
            "Let type checker refutes definition without type specified"
        );

        assert!(
            Fol::type_check_stm(
                &Global(
                    "o".to_string(),
                    Some(Predicate("StupidUnboundType".to_string(), vec![])),
                    Box::new(zero)
                ),
                &mut test_env,
            )
            .is_err(),
            "Let type checker accepts definition with declared unbound type"
        );
        assert!(
            Fol::type_check_stm(
                &Global(
                    "o".to_string(),
                    Some(nat.clone()),
                    Box::new(Variable("stupid_unbound_var".to_string()))
                ),
                &mut test_env,
            )
            .is_err(),
            "Let type checker accepts definition with ill typed body"
        );
    }
}

mod fun_stm {
    use super::*;

    #[test]
    fn test_fun_type_check() {
        let nat = Predicate("Nat".to_string(), vec![]);
        // let zero = Variable("zero".to_string());
        let mut test_env: Environment<Fol> =
            Environment::with_defaults(vec![], vec![], vec![("Nat", &vec![])]);

        let res = Fol::type_check_stm(
            &Fun(
                "f".to_string(),
                vec![("n".to_string(), nat.clone())],
                Box::new(nat.clone()),
                Box::new(Variable("n".to_string())),
                false,
            ),
            &mut test_env,
        );
        assert!(res.is_ok(), "Fun type checker failed with {:?}", res.err());
        assert_eq!(
            test_env.get_variable_type("f"),
            Some(Arrow(Box::new(nat.clone()), Box::new(nat.clone()))),
            "Fun type checker didnt update the context properly"
        );
        assert!(
            Fol::type_check_stm(
                &Fun(
                    "g".to_string(),
                    vec![("n".to_string(), nat.clone())],
                    Box::new(nat.clone()),
                    Box::new(Variable("n".to_string())),
                    false
                ),
                &mut test_env
            )
            .is_ok(),
            "Top level type checker doesnt support function definitions"
        );

        assert!(
            Fol::type_check_stm(
                &Fun(
                    "h".to_string(),
                    vec![("n".to_string(), Predicate("StupidUnboundName".to_string(), vec![]))],
                    Box::new(nat.clone()),
                    Box::new(Variable("n".to_string())),
                    false
                ),
                &mut test_env,
            ).is_err(),
            "Fun type checker accpets function definition with variable of unbound type"
        );
        assert!(
            Fol::type_check_stm(
                &Fun(
                    "h".to_string(),
                    vec![("n".to_string(), nat.clone())],
                    Box::new(nat.clone()),
                    Box::new(Variable("stupid_unbound_var".to_string())),
                    false
                ),
                &mut test_env,
            )
            .is_err(),
            "Fun type checker accpets function definition with ill typed body"
        );
        assert!(
            Fol::type_check_stm(
                &Fun(
                    "h".to_string(),
                    vec![("n".to_string(), nat.clone())],
                    Box::new(nat),
                    Box::new(Application(
                        Box::new(Variable("h".to_string())),
                        Box::new(Variable("n".to_string()))
                    )),
                    false
                ),
                &mut test_env,
            ).is_err(),
            "Fun type checker accpets normal function definition with recursive call"
        );
    }
}
