#[cfg(test)]
//TODO include tests for failure on non type expressions i dont
//want to do it now cuz i dont have a real way to distinguish them yet
mod unit_tests {
    use crate::parser::api::Statement;
    use crate::runtime::program::ProgramNode;
    use crate::type_theory::interface::TypeTheory;
    use crate::{
        misc::Union::{self, L, R},
        parser::api::Expression::{self},
        type_theory::fol::fol::{
            Fol,
            FolFormula::{Arrow, ForAll, Predicate},
            FolStm::Global,
            FolTerm::{Abstraction, Application, Let, Variable},
        },
    };

    #[test]
    fn test_var_elaboration() {
        assert_eq!(
            Fol::elaborate_expression(&Expression::VarUse("n".to_string())),
            Ok(Union::L(Variable("n".to_string()))),
            "Variable elaboration doesnt produce proper term"
        );
        assert_eq!(
            Fol::elaborate_expression(&Expression::VarUse("Nat".to_string())),
            Ok(Union::R(Predicate("Nat".to_string(), vec![]))),
            "Variable elaboration doesnt produce proper atomic type"
        );
        assert_eq!(
            Fol::elaborate_expression(&Expression::VarUse(
                "ListOfNat".to_string()
            )),
            Ok(Union::R(Predicate("ListOfNat".to_string(), vec![]))),
            "PascalCase doesnt return a type"
        );
        assert_eq!(
            Fol::elaborate_expression(&Expression::VarUse(
                "list_of_nat".to_string()
            )),
            Ok(Union::L(Variable("list_of_nat".to_string()))),
            "snake_case doesnt return a term"
        );
    }

    #[test]
    fn test_abstraction_elaboration() {
        assert_eq!(
            Fol::elaborate_expression(&Expression::Abstraction(
                "x".to_string(),
                Box::new(Expression::VarUse("Nat".to_string())),
                Box::new(Expression::VarUse("x".to_string())),
            )),
            Ok(L(Abstraction(
                "x".to_string(),
                Box::new(Predicate("Nat".to_string(), vec![])),
                Box::new(Variable("x".to_string())),
            ))),
            "Abstraction elaboration doesnt produce correct term "
        );
    }

    #[test]
    fn test_application_elaboration() {
        assert_eq!(
            Fol::elaborate_expression(&Expression::Application(
                Box::new(Expression::VarUse("f".to_string())),
                vec![Expression::VarUse("x".to_string())],
            )),
            Ok(L(Application(
                Box::new(Variable("f".to_string())),
                Box::new(Variable("x".to_string())),
            ))),
            "Application elaboration doesnt produce correct term"
        );
    }

    #[test]
    fn test_arrow_elaboration() {
        assert_eq!(
            Fol::elaborate_expression(&Expression::Arrow(
                Box::new(Expression::VarUse("Nat".to_string())),
                Box::new(Expression::VarUse("Bool".to_string())),
            )),
            Ok(R(Arrow(
                Box::new(Predicate("Nat".to_string(), vec![])),
                Box::new(Predicate("Bool".to_string(), vec![]))
            ))),
            "Arrow elaboration doesnt produce proper term"
        );
    }

    #[test]
    fn test_forall_elaboration() {
        assert_eq!(
            Fol::elaborate_expression(&Expression::TypeProduct(
                "n".to_string(),
                Box::new(Expression::VarUse("Nat".to_string())),
                Box::new(Expression::VarUse("Top".to_string())),
            )),
            Ok(Union::R(ForAll(
                "n".to_string(),
                Box::new(Predicate("Nat".to_string(), vec![])),
                Box::new(Predicate("Top".to_string(), vec![]))
            ))),
            "For all elaboration doesnt produce proper term"
        );
    }

    #[test]
    fn test_let_elaboration() {
        assert_eq!(
            Fol::elaborate_expression(&Expression::Let(
                "x".to_string(),
                Box::new(None),
                Box::new(Expression::VarUse("i".to_string())),
                Box::new(Expression::VarUse("x".to_string())),
            )),
            Ok(L(Let(
                "x".to_string(),
                Box::new(None),
                Box::new(Variable("i".to_string())),
                Box::new(Variable("x".to_string())),
            ))),
            "Let elaboration isnt producing the proper term"
        );
    }

    // TODO support this test too
    // #[test]
    // fn test_fun_elaboration() {}

    #[test]
    fn test_global_elaboration() {
        let res = Fol::elaborate_statement(&Statement::Global(
            "n".to_string(),
            Some(Expression::VarUse("Nat".to_string())),
            Expression::VarUse("zero".to_string()),
        ));
        let expected_let = Global(
            "n".to_string(),
            Some(Predicate("Nat".to_string(), vec![])),
            Box::new(Variable("zero".to_string())),
        );

        assert!(
            res.is_ok(),
            "Let elaboration failed with {}",
            res.err().unwrap()
        );
        assert_eq!(
            res.unwrap().peek_first().unwrap(),
            &ProgramNode::OfStm(expected_let),
            "Let elaboration doesn't return proper statement"
        );
    }
}
