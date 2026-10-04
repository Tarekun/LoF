#[cfg(test)]
mod unit_tests {
    use crate::{
        error::LofError,
        tptp::thf::{thf_formula, thf_input, ThfInput},
        type_theory::cic::cic::{
            CicTerm::{
                self, Abstraction, Application, Meta, Product, Sort, Variable,
            },
            NameKind, HOLE_INDEX,
        },
    };

    /// Parses `input` expecting it to be entirely consumed
    fn parse(input: &str) -> Result<CicTerm, LofError> {
        match thf_formula(input) {
            Ok(("", term)) => Ok(term),
            Ok((rest, _)) => {
                Err(LofError::custom(format!("leftover: {}", rest)))
            }
            Err(err) => Err(err.into()),
        }
    }

    fn c(name: &str) -> CicTerm {
        Variable(name.to_string(), NameKind::Const())
    }
    fn bound(name: &str, index: i32) -> CicTerm {
        Variable(name.to_string(), NameKind::Bound(index))
    }
    fn app(fun: CicTerm, args: Vec<CicTerm>) -> CicTerm {
        args.into_iter()
            .fold(fun, |fun, arg| Application(Box::new(fun), Box::new(arg)))
    }
    fn arrow(domain: CicTerm, codomain: CicTerm) -> CicTerm {
        Product("_".to_string(), Box::new(domain), Box::new(codomain))
    }
    fn lambda(var: &str, typee: CicTerm, body: CicTerm) -> CicTerm {
        Abstraction(var.to_string(), Box::new(typee), Box::new(body))
    }
    fn hole() -> CicTerm {
        Meta(HOLE_INDEX)
    }

    #[test]
    fn test_application_and_types() {
        assert_eq!(
            parse("f @ a @ (g @ b)"),
            Ok(app(c("f"), vec![c("a"), app(c("g"), vec![c("b")])])),
            "Application chains arent left associative"
        );
        assert_eq!(
            parse("($i > $o) > $o > $o"),
            Ok(arrow(arrow(c("$i"), c("$o")), arrow(c("$o"), c("$o")))),
            "Mapping types arent right associative products"
        );
        assert_eq!(parse("$tType"), Ok(Sort("TYPE".to_string())));
    }

    #[test]
    fn test_connectives() {
        let (p, q, r) = (c("p"), c("q"), c("r"));
        assert_eq!(
            parse("p & q & r"),
            Ok(app(
                c("&"),
                vec![app(c("&"), vec![p.clone(), q.clone()]), r.clone()]
            )),
            "Conjunction chains arent left associative"
        );
        assert_eq!(
            parse("p <= q"),
            Ok(app(c("=>"), vec![q.clone(), p.clone()]))
        );
        assert_eq!(
            parse("p ~| q"),
            Ok(app(c("~"), vec![app(c("|"), vec![p.clone(), q.clone()])]))
        );
        assert_eq!(
            parse("a = b => a != b"),
            Ok(app(
                c("=>"),
                vec![
                    app(c("="), vec![hole(), c("a"), c("b")]),
                    app(
                        c("~"),
                        vec![app(c("="), vec![hole(), c("a"), c("b")])]
                    ),
                ]
            )),
            "Equations dont leave their type argument as a hole"
        );
        assert!(
            parse("p | q & r").is_err(),
            "Mixed connectives without parentheses are accepted"
        );
        assert!(
            parse("p @ a & q").is_err(),
            "Applications mixed with connectives without parentheses are accepted"
        );
    }

    #[test]
    fn test_binders() {
        assert_eq!(
            parse("! [X: $i, Y: $i] : (p @ X @ Y)"),
            Ok(app(
                c("!!"),
                vec![
                    c("$i"),
                    lambda(
                        "X",
                        c("$i"),
                        app(
                            c("!!"),
                            vec![
                                c("$i"),
                                lambda(
                                    "Y",
                                    c("$i"),
                                    app(c("p"), vec![bound("X", 1), bound("Y", 0)])
                                )
                            ]
                        )
                    )
                ]
            )),
            "Universal quantifiers arent `!!` applied to the variable type and a λ"
        );
        assert_eq!(
            parse("^ [F: $i > $o] : (?? @ F)"),
            Ok(lambda(
                "F",
                arrow(c("$i"), c("$o")),
                app(c("??"), vec![hole(), bound("F", 0)])
            )),
            "λ-abstractions or quantifiers as terms arent parsed"
        );
        assert_eq!(
            parse("!> [A: $tType] : (A > A)"),
            Ok(Product(
                "A".to_string(),
                Box::new(Sort("TYPE".to_string())),
                Box::new(arrow(bound("A", 0), bound("A", 1)))
            )),
            "Type quantification isnt a product with closed De Bruijn indices"
        );
    }

    #[test]
    fn test_declarations() {
        assert_eq!(
            thf_input("list: $tType > $tType"),
            Ok((
                "",
                ThfInput::Declaration(
                    "list".to_string(),
                    arrow(Sort("TYPE".to_string()), Sort("TYPE".to_string()))
                )
            ))
        );
        assert_eq!(
            thf_input("(p: $i > $o)"),
            Ok((
                "",
                ThfInput::Declaration("p".to_string(), arrow(c("$i"), c("$o")))
            ))
        );
        assert_eq!(
            thf_input("p @ a"),
            Ok(("", ThfInput::Formula(app(c("p"), vec![c("a")])))),
            "Formulas are taken for declarations"
        );
    }
}
