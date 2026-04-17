#[cfg(test)]
mod unit_tests {
    use crate::{
        config::Config,
        parser::api::{Expression, LofParser},
    };

    #[test]
    fn test_identifier() {
        let parser = LofParser::new(Config::default());
        assert!(
            parser.parse_identifier("test").is_ok(),
            "Parser cant read identifiers"
        );
        assert_eq!(
            parser.parse_identifier("  test").unwrap(),
            ("", "test"),
            "Identifier parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_identifier("test123").is_ok(),
            "Identifier parser cant read numbers/underscores"
        );
        assert!(
            parser.parse_identifier("_snake_case_").is_ok(),
            "Identifier parser cant read snake case name"
        );
        assert!(
            parser.parse_identifier("Γφ").is_ok(),
            "Identifier parser cant read greek letters"
        );
    }

    #[test]
    fn test_type_expression() {
        let parser = LofParser::new(Config::default());
        assert_eq!(
            parser.parse_type_expression("TYPE").unwrap(),
            ("", (Expression::VarUse("TYPE".to_string()))),
            "parse_type_expression cant read simple sorts"
        );
        assert!(
            parser.parse_type_expression("A -> B").is_ok(),
            "parse_type_expression cant read arrow types"
        );
        assert!(
            parser.parse_type_expression("(ΠT:TYPE.T)").is_ok(),
            "parse_type_expression cant read types enclosed in parethesis"
        );
    }

    #[test]
    fn test_typed_identifier() {
        let parser = LofParser::new(Config::default());
        assert_eq!(
            parser.parse_typed_identifier("x : TYPE").unwrap(),
            (
                "",
                ("x".to_string(), Expression::VarUse("TYPE".to_string()))
            ),
            "parse_typed_identifier doesnt return as expected"
        );
        assert_eq!(
            parser
                .parse_typed_identifier("\r\tx \t  : \t  TYPE")
                .unwrap(),
            (
                "",
                ("x".to_string(), Expression::VarUse("TYPE".to_string()))
            ),
            "parse_typed_identifier cant cope with whitespaces"
        );
        assert!(
            parser.parse_typed_identifier("x:TYPE").is_ok(),
            "parse_typed_identifier cant cope with dense notation"
        );
    }
}
