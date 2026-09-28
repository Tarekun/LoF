use crate::type_theory::{
    environment::Environment,
    f::f::{
        FStm::{Axiom, Global},
        SystemF,
    },
    grammars::f::{
        FTerm::{
            self, Abstraction, Application, TypeAbstraction, TypeApplication,
            Variable,
        },
        FType::{self, Arrow, Atomic, Forall, MetaVariable},
    },
    interface::{Kernel, TypeTheory},
};

fn var(name: &str) -> FTerm {
    Variable(name.to_string())
}
fn ty(name: &str) -> FType {
    Atomic(name.to_string())
}
fn kind() -> FType {
    ty("*")
}
fn arrow(domain: FType, codomain: FType) -> FType {
    Arrow(Box::new(domain), Box::new(codomain))
}
fn forall(var_name: &str, body: FType) -> FType {
    Forall(var_name.to_string(), Box::new(kind()), Box::new(body))
}
fn lambda(var_name: &str, var_type: FType, body: FTerm) -> FTerm {
    Abstraction(var_name.to_string(), var_type, Box::new(body))
}
fn type_lambda(var_name: &str, body: FTerm) -> FTerm {
    TypeAbstraction(var_name.to_string(), Box::new(kind()), Box::new(body))
}
fn app(fun: FTerm, arg: FTerm) -> FTerm {
    Application(Box::new(fun), Box::new(arg))
}
fn type_app(fun: FTerm, type_arg: FType) -> FTerm {
    TypeApplication(Box::new(fun), type_arg)
}

/// Environment with the base types `nat` and `bool`, and `zero: nat`
fn test_env() -> Environment<SystemF> {
    let mut env = SystemF::default_environment();
    env.add_to_context("nat", &kind());
    env.add_to_context("bool", &kind());
    env.add_to_context("zero", &ty("nat"));
    env.add_to_context("not", &arrow(ty("bool"), ty("bool")));
    env
}

mod variable {
    use super::*;

    #[test]
    fn test_variable_type_check() {
        let mut env = test_env();
        assert_eq!(
            SystemF::type_check_term(&var("zero"), &mut env),
            Ok(ty("nat"))
        );
        assert!(
            SystemF::type_check_term(&var("unbound"), &mut env).is_err(),
            "Variable type checking accepts unbound variables"
        );
        assert!(
            SystemF::type_check_term(&var("nat"), &mut env).is_err(),
            "Variable type checking accepts types as terms"
        );
    }
}

mod abstraction {
    use super::*;

    #[test]
    fn test_abstraction_type_check() {
        let mut env = test_env();
        assert_eq!(
            SystemF::type_check_term(
                &lambda("x", ty("nat"), var("x")),
                &mut env
            ),
            Ok(arrow(ty("nat"), ty("nat")))
        );
        assert!(
            env.get_variable_type("x").is_none(),
            "Abstraction type checking leaks its variable in the context"
        );
        assert!(
            SystemF::type_check_term(
                &lambda("x", ty("unbound"), var("x")),
                &mut env
            )
            .is_err(),
            "Abstraction type checking accepts undeclared argument types"
        );
        assert!(
            SystemF::type_check_term(&lambda("x", kind(), var("x")), &mut env)
                .is_err(),
            "Abstraction type checking accepts abstraction over types"
        );
    }
}

mod application {
    use super::*;

    #[test]
    fn test_application_type_check() {
        let mut env = test_env();
        assert_eq!(
            SystemF::type_check_term(
                &app(lambda("x", ty("nat"), var("x")), var("zero")),
                &mut env
            ),
            Ok(ty("nat"))
        );
        assert!(
            SystemF::type_check_term(&app(var("not"), var("zero")), &mut env)
                .is_err(),
            "Application type checking accepts arguments of the wrong type"
        );
        assert!(
            SystemF::type_check_term(&app(var("zero"), var("zero")), &mut env)
                .is_err(),
            "Application type checking accepts non functional terms"
        );
    }
}

mod polymorphism {
    use super::*;

    #[test]
    fn test_type_abstraction_type_check() {
        let mut env = test_env();
        let id = type_lambda("A", lambda("x", ty("A"), var("x")));
        assert_eq!(
            SystemF::type_check_term(&id, &mut env),
            Ok(forall("A", arrow(ty("A"), ty("A"))))
        );
        assert!(
            env.get_variable_type("A").is_none(),
            "Type abstraction type checking leaks its type variable"
        );
        assert!(
            SystemF::type_check_term(
                &TypeAbstraction(
                    "A".to_string(),
                    Box::new(arrow(kind(), kind())),
                    Box::new(var("zero"))
                ),
                &mut env
            )
            .is_err(),
            "Type abstraction accepts higher kinds (System Fω)"
        );
    }

    #[test]
    fn test_type_application_type_check() {
        let mut env = test_env();
        let id = type_lambda("A", lambda("x", ty("A"), var("x")));

        assert_eq!(
            SystemF::type_check_term(
                &type_app(id.clone(), ty("nat")),
                &mut env
            ),
            Ok(arrow(ty("nat"), ty("nat"))),
            "Type application doesnt instantiate the polymorphic type"
        );
        assert_eq!(
            SystemF::type_check_term(
                &app(type_app(id.clone(), ty("nat")), var("zero")),
                &mut env
            ),
            Ok(ty("nat"))
        );
        assert!(
            SystemF::type_check_term(
                &app(type_app(id.clone(), ty("bool")), var("zero")),
                &mut env
            )
            .is_err(),
            "Instantiated polymorphic function accepts arguments of the wrong type"
        );
        assert!(
            SystemF::type_check_term(
                &type_app(var("zero"), ty("nat")),
                &mut env
            )
            .is_err(),
            "Type application accepts non polymorphic terms"
        );
        assert!(
            SystemF::type_check_term(&type_app(id, ty("unbound")), &mut env)
                .is_err(),
            "Type application accepts undeclared types"
        );
    }

    #[test]
    fn test_alpha_equivalent_types_are_equal() {
        let mut env = test_env();
        // (λf: ∀B. B → B. f) (ΛA. λx:A. x)
        let term = app(
            lambda("f", forall("B", arrow(ty("B"), ty("B"))), var("f")),
            type_lambda("A", lambda("x", ty("A"), var("x"))),
        );
        assert!(
            SystemF::type_check_term(&term, &mut env).is_ok(),
            "Type equality isnt up to renaming of bound type variables"
        );
    }
}

mod types {
    use super::*;

    #[test]
    fn test_type_well_formedness() {
        let mut env = test_env();
        assert_eq!(SystemF::type_check_type(&ty("nat"), &mut env), Ok(kind()));
        assert_eq!(
            SystemF::type_check_type(
                &forall("A", arrow(ty("A"), ty("nat"))),
                &mut env
            ),
            Ok(kind())
        );
        assert!(
            SystemF::type_check_type(&ty("unbound"), &mut env).is_err(),
            "Undeclared types are well formed"
        );
        assert!(
            SystemF::type_check_type(&ty("zero"), &mut env).is_err(),
            "Terms are accepted as types"
        );
        assert!(
            SystemF::type_check_type(&arrow(ty("A"), ty("nat")), &mut env)
                .is_err(),
            "Unbound type variables are well formed"
        );
        assert!(
            SystemF::type_check_type(&arrow(kind(), ty("nat")), &mut env)
                .is_err(),
            "The kind is accepted as a proper type"
        );
        assert!(
            SystemF::type_check_type(&MetaVariable("m".to_string()), &mut env)
                .is_err(),
            "Metavariables are accepted without type inference"
        );
    }
}

mod statements {
    use super::*;

    #[test]
    fn test_axiom_type_check() {
        let mut env = test_env();
        assert!(
            SystemF::type_check_stm(
                &Axiom("list".to_string(), kind()),
                &mut env
            )
            .is_ok(),
            "Base type declarations dont type check"
        );
        assert!(
            SystemF::type_check_type(&ty("list"), &mut env).is_ok(),
            "Declared base types arent added to the environment"
        );
        assert!(SystemF::type_check_stm(
            &Axiom("nil".to_string(), ty("list")),
            &mut env
        )
        .is_ok());
        assert_eq!(env.get_variable_type("nil"), Some(ty("list")));
        assert!(
            SystemF::type_check_stm(
                &Axiom("bad".to_string(), ty("unbound")),
                &mut env
            )
            .is_err(),
            "Axioms of undeclared types are accepted"
        );
    }

    #[test]
    fn test_global_type_check() {
        let mut env = test_env();
        let id = type_lambda("A", lambda("x", ty("A"), var("x")));
        assert!(SystemF::type_check_stm(
            &Global(
                "id".to_string(),
                Some(forall("B", arrow(ty("B"), ty("B")))),
                id.clone()
            ),
            &mut env
        )
        .is_ok());
        assert_eq!(
            SystemF::type_check_term(
                &app(type_app(var("id"), ty("nat")), var("zero")),
                &mut env
            ),
            Ok(ty("nat")),
            "Global definitions arent added to the environment"
        );
        assert!(
            SystemF::type_check_stm(
                &Global("bad".to_string(), Some(ty("nat")), id),
                &mut env
            )
            .is_err(),
            "Globals with a mismatching type annotation are accepted"
        );
    }
}
