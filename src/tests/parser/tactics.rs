#[cfg(test)]
mod unit_tests {
    use crate::{
        config::Config,
        parser::api::Expression::VarUse,
        parser::api::LofParser,
        parser::api::Tactic::{Apply, Begin, Exact, Intro, Qed},
    };

    #[test]
    fn test_interactive_proof() {
        let parser = LofParser::new(Config::default());

        assert_eq!(
            parser.parse_interactive_proof("begin qed."),
            Ok(("", vec![Begin(), Qed()])),
            "Interactive proof parser doesnt construct proper AST"
        );
        assert!(
            parser.parse_interactive_proof("begin").is_ok(),
            "Interactive proof parser doesnt read partial proof"
        );
        assert!(
            parser.parse_interactive_proof("intro n:Nat").is_err(), 
            "Interactive proof parser reads a proof that doesnt start with begin tactic"
        );
    }

    #[test]
    fn test_intro() {
        let parser = LofParser::new(Config::default());

        assert_eq!(
            parser.parse_tactic("intro n:Nat"),
            Ok(("", Intro("n".to_string(), VarUse("Nat".to_string())))),
            "Intro parser doesnt construct the proper node"
        );
        assert!(
            parser
                .parse_tactic("\n\r\t intro   \t n\t:\t \rNat   ")
                .is_ok(),
            "Intro parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_tactic("intro Q : ∀n:Nat. P n").is_ok(),
            "Intro parser cant cope with more complex type expressions"
        );
        assert!(
            parser.parse_tactic("intro:Nat").is_err(),
            "Intro parser doesnt split keyword and variable names"
        );
    }

    #[test]
    fn test_exact() {
        let parser = LofParser::new(Config::default());

        assert_eq!(
            parser.parse_tactic("exact p"),
            Ok(("", Exact(VarUse("p".to_string())))),
            "Exact parser doesnt construct the proper node"
        );

        assert!(
            parser.parse_tactic("\n\t      \r\n \t exact  \t p").is_ok(),
            "Exact parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_tactic("exact λn:Nat.n").is_ok(),
            "Exact parser cant cope with composite terms"
        );
    }

    #[test]
    fn test_apply() {
        let parser = LofParser::new(Config::default());

        assert_eq!(
            parser.parse_tactic("apply h"),
            Ok(("", Apply(VarUse("h".to_string())))),
            "Apply parser doesnt construct the proper node"
        );
        assert!(
            parser.parse_tactic("\n\r\t apply   \t h\t").is_ok(),
            "Apply parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_tactic("apply f x y").is_ok(),
            "Apply parser cant cope with function application expressions"
        );
        assert!(
            parser.parse_tactic("applyh").is_err(),
            "Apply parser doesnt split keyword and argument"
        );
    }
}
//########################### UNIT TESTS
