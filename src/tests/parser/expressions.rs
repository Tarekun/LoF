#[cfg(test)]
mod unit_tests {
    use crate::{
        config::Config,
        parser::api::{
            Expression::{
                Abstraction, Application, Arrow, Inferator, Let, Match, Pipe,
                Tuple, TypeProduct, VarUse,
            },
            LofParser,
        },
    };

    #[test]
    fn test_notation() {
        let parser = LofParser::new(Config::default());

        let _ = parser.parse_notation("sugar \"_0 + _1\" := \"add _0 _1\"");
        assert_eq!(
            parser.parse_expression("n + m"),
            Ok((
                "",
                Application(
                    Box::new(VarUse("add".to_string())),
                    vec![VarUse("n".to_string()), VarUse("m".to_string())]
                )
            )),
            "Parser couldnt pick up simple binary infix custom notation"
        );
        assert_eq!(
            parser.parse_expression("n   \t\r +   \t\t\nm"),
            Ok((
                "",
                Application(
                    Box::new(VarUse("add".to_string())),
                    vec![VarUse("n".to_string()), VarUse("m".to_string())]
                )
            )),
            "Custom notation parser cant cope with whitespaces"
        );
        // assert_eq!(
        //     parser.parse_expression("(n + m) + o"),
        //     Ok((
        //         "",
        //         Application(
        //             Box::new(VarUse("add".to_string())),
        //             vec![
        //                 Application(
        //                     Box::new(VarUse("add".to_string())),
        //                     vec![
        //                         VarUse("n".to_string()),
        //                         VarUse("m".to_string()),
        //                     ]
        //                 ),
        //                 VarUse("o".to_string())
        //             ]
        //         )
        //     )),
        //     "Composed applications don't parse properly"
        // );
        let _ = parser.parse_notation("sugar \"_0 ++ _1\" := \"add _1 _0\"");
        assert_eq!(
            parser.parse_expression("n ++ m"),
            Ok((
                "",
                Application(
                    Box::new(VarUse("add".to_string())),
                    vec![VarUse("m".to_string()), VarUse("n".to_string())]
                )
            )),
            "Custom notation parser cant track arguments properly"
        );

        let _ = parser.parse_notation("sugar \"_h :: _l\" := \"cons ? _h _l\"");
        assert_eq!(
            parser.parse_expression("h :: l"),
            Ok((
                "",
                Application(
                    Box::new(VarUse("cons".to_string())),
                    vec![
                        Inferator(),
                        VarUse("h".to_string()),
                        VarUse("l".to_string())
                    ]
                )
            )),
            "Custom notation parser list doenst work properly"
        );
    }

    #[test]
    fn test_parens() {
        let parser = LofParser::new(Config::default());
        assert!(
            parser.parse_expression("(x)").is_ok(),
            "Parser cant cope with parenthesis"
        );
        assert!(
            parser.parse_expression("((x))").is_ok(),
            "Parser cant cope with nested parenthesis"
        );
        assert!(
            parser.parse_expression("(x").is_err(),
            "Parser accepts unmatched parenthesis"
        );
        assert!(
            // this must use parens specifically or 'x' will be parsed as a variable
            parser.parse_parens("x)").is_err(),
            "Parser accepts unmatched parenthesis"
        );
        assert_eq!(
            parser.parse_expression("(x)").unwrap(),
            ("", VarUse("x".to_string())),
            "Parenthesis parser doesnt produce subterm properly"
        );
    }

    #[test]
    fn test_var() {
        let parser = LofParser::new(Config::default());
        assert!(
            parser.parse_expression("test").is_ok(),
            "Parser cant read variables"
        );
        assert_eq!(
            parser.parse_expression("  test\n").unwrap(),
            ("\n", VarUse("test".to_string())),
            "Variable parser cant cope with whitespaces"
        );
    }

    #[test]
    fn test_abs() {
        let parser = LofParser::new(Config::default());

        assert!(
            parser.parse_expression("λx:T.x").is_ok(),
            "Parser cant read lambda abstractions"
        );
        assert_eq!(
            parser.parse_expression("λn:nat.n").unwrap(),
            (
                "",
                Abstraction(
                    "n".to_string(),
                    Box::new(VarUse("nat".to_string())),
                    Box::new(VarUse("n".to_string()))
                )
            ),
            "Abstraction struct isnt properly built"
        );
        assert!(
            parser
                .parse_expression("λ \tx   :\tT \t . \t x  \n")
                .is_ok(),
            "Abstraction parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_expression("\\lambda   x :T .  x").is_ok(),
            "Abstraction parser cant use 'lambda' keyword"
        );
        assert_eq!(
            parser.parse_expression("λ. TYPE"),
            Ok((
                "",
                Abstraction(
                    "it".to_string(),
                    Box::new(VarUse("Unit".to_string())),
                    Box::new(VarUse("TYPE".to_string()))
                )
            ),),
            "Abstraction parser doesnt construct proper argumentless abstraction"
        )
    }

    #[test]
    fn test_type_abs() {
        let parser = LofParser::new(Config::default());

        assert!(
            parser.parse_expression("ΠT:TYPE.T").is_ok(),
            "Parser cant read type abstractions"
        );
        assert!(
            parser
                .parse_expression("Π \tT   :\tTYPE \t . \t T  \n")
                .is_ok(),
            "Type abstraction parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_expression("\\forall   T :TYPE .  T").is_ok(),
            "Type abstraction parser cant use 'forall' keyword"
        );
        assert_eq!(
            parser.parse_expression("ΠT:TYPE.T").unwrap(),
            (
                "",
                TypeProduct(
                    "T".to_string(),
                    Box::new(VarUse("TYPE".to_string())),
                    Box::new(VarUse("T".to_string()))
                )
            ),
            "Abstraction struct isnt properly built"
        );
    }

    #[test]
    fn test_application() {
        let parser = LofParser::new(Config::default());
        assert_eq!(
            parser.parse_expression("f x").unwrap(),
            (
                "",
                Application(
                    Box::new(VarUse("f".to_string())),
                    vec![VarUse("x".to_string())]
                )
            ),
            "Parser cant read function application"
        );

        assert_eq!(
            parser.parse_expression("f x y z").unwrap(),
            (
                "",
                Application(
                    Box::new(VarUse("f".to_string())),
                    vec![
                        VarUse("x".to_string()),
                        VarUse("y".to_string()),
                        VarUse("z".to_string())
                    ]
                )
            ),
            "Parser should implement left-associative application"
        );

        assert_eq!(
            parser.parse_expression("f (x y) z").unwrap(),
            (
                "",
                Application(
                    Box::new(VarUse("f".to_string())),
                    vec![
                        Application(
                            Box::new(VarUse("x".to_string())),
                            vec![VarUse("y".to_string())],
                        ),
                        VarUse("z".to_string())
                    ]
                )
            ),
            "Application parser messes up associativity with parenthesis"
        );
    }

    #[test]
    fn test_arrow_expression() {
        let parser = LofParser::new(Config::default());
        assert_eq!(
            parser.parse_expression("A -> B").unwrap(),
            (
                "",
                Arrow(
                    Box::new(VarUse("A".to_string())),
                    Box::new(VarUse("B".to_string()))
                )
            ),
            "Parser cant read type arrow expressions"
        );
        assert!(
            parser.parse_expression(" \tA   \t \t -> \t B  \n").is_ok(),
            "Arrow expression parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_expression("A->B").is_ok(),
            "Arrow expression parser cant cope with dense notation"
        );
    }

    #[test]
    fn test_let() {
        let parser = LofParser::new(Config::default());

        assert!(
            parser.parse_expression("let z: Nat := zero;\nbody").is_ok(),
            "Parser cant read let definitions"
        );
        assert!(
            parser
                .parse_expression(
                    "let \t x  \t:  \t Nat  :=\t  x;  \t\n\r\t\t x"
                )
                .is_ok(),
            "Let parser cant cope with multispaces"
        );
        // assert!(
        //     parser.let_def("letn :Nat:= zero;\n n").is_err(),
        //     "Let parser doesnt split 'let' keyword and variable identifier"
        // );
        assert!(
            parser.parse_expression("let n := zero;\n n").is_ok(),
            "Let parser doesnt support untyped definition"
        );
        assert_eq!(
            parser.parse_expression("let n : Nat := zero; n").unwrap(),
            (
                "",
                Let(
                    "n".to_string(),
                    Box::new(Some(VarUse("Nat".to_string()))),
                    Box::new(VarUse("zero".to_string())),
                    Box::new(VarUse("n".to_string()))
                )
            ),
            "Let definition struct isnt properly constructed"
        );
        assert!(
            parser.parse_node("let z: Nat := zero;\nbody").is_ok(),
            "Top level parser cant read let definitions"
        );
    }

    #[test]
    fn test_let_support() {
        let parser = LofParser::new(Config::default());

        assert!(
            parser.local_expression("let n : Nat := zero;\n  n").is_ok(),
            "Dedicated top-level parser still doesnt work with let definitions"
        );
        assert!(
            parser
                .parse_statement("fun f (x: X) : X { let y := x; x }")
                .is_ok(),
            "Function parser doesnt support let definition in the function body"
        );
    }

    #[test]
    fn test_pattern_matching() {
        let parser = LofParser::new(Config::default());

        assert_eq!(
            parser.parse_expression("match x with | O => x,").unwrap(),
            (
                "",
                Match(
                    Box::new(VarUse("x".to_string())),
                    vec![(VarUse("O".to_string()), VarUse("x".to_string()))]
                )
            ),
            "Pattern match expression isnt properly constructed"
        );
        assert!(
            parser
                .parse_expression("match \tx   with \n\t|O =>  \nx   , \n ")
                .is_ok(),
            "Pattern match parser cant cope with whitespaces"
        );
        // assert!(
        //     parser.parse_pattern_match("matchx with | O => x,").is_err(),
        //     "Pattern match parser doesnt split keywords"
        // );
        assert!(
            parser.parse_expression("match xwith | O => x,").is_err(),
            "Pattern match parser doesnt split keywords"
        );
    }

    #[test]
    fn test_pipe_expression() {
        let parser = LofParser::new(Config::default());

        assert_eq!(
            parser.parse_expression("A | B").unwrap(),
            (
                "",
                Pipe(vec![VarUse("A".to_string()), VarUse("B".to_string())])
            ),
            "Pipe expression for union type isnt working"
        );
        assert_eq!(
            parser.parse_expression("A | B").unwrap(),
            (
                "",
                Pipe(vec![VarUse("A".to_string()), VarUse("B".to_string())])
            ),
            "Top level expression parser doesnt support pipes"
        );

        assert_eq!(
            parser.parse_expression("A | B | C | D").unwrap(),
            (
                "",
                Pipe(vec![
                    VarUse("A".to_string()),
                    VarUse("B".to_string()),
                    VarUse("C".to_string()),
                    VarUse("D".to_string()),
                ])
            ),
            "Pipe expression doesnt support n-ary unions"
        );

        assert_eq!(
            parser.parse_expression("A \n\t \r   |  \n \r\tB").unwrap(),
            (
                "",
                Pipe(vec![VarUse("A".to_string()), VarUse("B".to_string())])
            ),
            "Pipe expression cant cope with whitespaces"
        );
    }

    #[test]
    fn test_tuple() {
        let parser = LofParser::new(Config::default());

        assert_eq!(
            parser.parse_expression("(one, two, three)"),
            Ok((
                "",
                Tuple(vec![
                    VarUse("one".to_string()),
                    VarUse("two".to_string()),
                    VarUse("three".to_string()),
                ])
            )),
            "Tuple parser isnt working properly"
        );
        assert!(
            parser.parse_expression("(one, two, three,)").is_ok(),
            "Tuple parser doesnt support optional trailing comma"
        );
        assert!(
            parser
                .parse_expression(
                    "(  \n\t one,  \n\r   two   \t , \r\r\t three   \n)"
                )
                .is_ok(),
            "Tuple parser cant cope with whitespaces"
        );

        assert_eq!(
            parser.parse_expression("(one)"),
            Ok(("", VarUse("one".to_string()),)),
            "Tuple parser parser likely conflicts with the parenthesis one"
        );
        assert_eq!(
            parser.parse_expression("(one,)"),
            Ok(("", Tuple(vec![VarUse("one".to_string())]))),
            "Singleton tuples cant be parsed properly"
        );
    }

    #[test]
    fn test_infer_operator() {
        let parser = LofParser::new(Config::default());

        assert!(
            parser.parse_expression("?").is_ok(),
            "parser doesnt support the infer operator ?"
        );

        assert!(
            parser.parse_expression("\n  \t\r\r\t  ? ").is_ok(),
            "parser doesnt support the infer operator ? preceeded by whitespaces"
        );

        assert_eq!(
            parser.parse_expression("cons ? z l"),
            Ok((
                "",
                Application(
                    Box::new(VarUse("cons".to_string())),
                    vec![
                        Inferator(),
                        VarUse("z".to_string()),
                        VarUse("l".to_string())
                    ]
                )
            )),
            "Metavariable parser doesnt integrate with applications"
        )
    }
}
