#[cfg(test)]
mod unit_tests {
    use std::collections::BTreeMap;

    use crate::{
        error::LofError,
        tptp::fof::{fof_formula, tff_formula, Symbols},
        type_theory::grammars::fol::{
            FolFormula::{
                self, Arrow, Conjunction, Disjunction, Exist, ForAll, Not,
                Predicate,
            },
            FolTerm::{self, Variable},
        },
    };

    fn var(name: &str) -> FolTerm {
        Variable(name.to_string())
    }
    fn pred(name: &str, args: Vec<FolTerm>) -> FolFormula {
        Predicate(name.to_string(), args)
    }
    fn atom(name: &str) -> FolFormula {
        pred(name, vec![])
    }
    fn not(φ: FolFormula) -> FolFormula {
        Not(Box::new(φ))
    }
    fn arrow(l: FolFormula, r: FolFormula) -> FolFormula {
        Arrow(Box::new(l), Box::new(r))
    }
    fn sort() -> Box<FolFormula> {
        Box::new(atom("$i"))
    }
    fn forall(var: &str, body: FolFormula) -> FolFormula {
        ForAll(var.to_string(), sort(), Box::new(body))
    }
    fn exists(var: &str, body: FolFormula) -> FolFormula {
        Exist(var.to_string(), sort(), Box::new(body))
    }

    /// Parses `input` expecting it to be entirely consumed
    fn parse(input: &str) -> Result<FolFormula, LofError> {
        match fof_formula(input) {
            Ok(("", (φ, _))) => Ok(φ),
            Ok((rest, _)) => {
                Err(LofError::custom(format!("leftover: {}", rest)))
            }
            Err(err) => Err(err.into()),
        }
    }

    #[test]
    fn test_binary_connectives() {
        let (p, q) = (atom("p"), atom("q"));
        let iff = Conjunction(vec![
            arrow(p.clone(), q.clone()),
            arrow(q.clone(), p.clone()),
        ]);

        assert_eq!(parse("p => q"), Ok(arrow(p.clone(), q.clone())));
        assert_eq!(parse("p <= q"), Ok(arrow(q.clone(), p.clone())));
        assert_eq!(parse("p <=> q"), Ok(iff.clone()));
        assert_eq!(parse("p <~> q"), Ok(not(iff)));
        assert_eq!(
            parse("p ~| q"),
            Ok(not(Disjunction(vec![p.clone(), q.clone()])))
        );
        assert_eq!(
            parse("p ~& q"),
            Ok(not(Conjunction(vec![p.clone(), q.clone()])))
        );
    }

    #[test]
    fn test_associative_connectives() {
        assert_eq!(
            parse("p | q | ~r"),
            Ok(Disjunction(vec![atom("p"), atom("q"), not(atom("r"))])),
            "FOF parser doesnt flatten disjunction chains"
        );
        assert_eq!(
            parse("p & (q | r) & s"),
            Ok(Conjunction(vec![
                atom("p"),
                Disjunction(vec![atom("q"), atom("r")]),
                atom("s"),
            ])),
            "FOF parser doesnt flatten conjunction chains"
        );
        assert!(
            parse("p | q & r").is_err(),
            "FOF parser accepts mixed connectives without parentheses"
        );
        assert!(
            parse("p => q => r").is_err(),
            "FOF parser accepts chained non associative connectives"
        );
    }

    #[test]
    fn test_quantifiers() {
        assert_eq!(
            parse("! [X, Y] : ? [Z] : p(X, Y, Z)"),
            Ok(forall(
                "X",
                forall(
                    "Y",
                    exists("Z", pred("p", vec![var("X"), var("Y"), var("Z")]))
                )
            )),
            "FOF parser doesnt handle variable lists"
        );
        assert_eq!(
            parse("![X]: p(X) & q"),
            Ok(Conjunction(vec![
                forall("X", pred("p", vec![var("X")])),
                atom("q")
            ])),
            "The body of a quantifier should be a unit formula"
        );
        assert_eq!(
            parse("~ ![X]: (p(X) => q(X))"),
            Ok(not(forall(
                "X",
                arrow(pred("p", vec![var("X")]), pred("q", vec![var("X")]))
            )))
        );
    }

    #[test]
    fn test_unbound_variables() {
        assert_eq!(
            parse("p(X)"),
            Err(LofError::unbound_variable("X")),
            "FOF parser accepts free variables"
        );
        assert_eq!(
            parse("(![X]: p(X)) & q(X)"),
            Err(LofError::unbound_variable("X")),
            "FOF parser leaks bound variables outside their scope"
        );
    }

    #[test]
    fn test_rectification() {
        assert_eq!(
            parse("(?[X]: p(X)) & (?[X]: q(X))"),
            Ok(Conjunction(vec![
                exists("X", pred("p", vec![var("X")])),
                exists("X_1", pred("q", vec![var("X_1")])),
            ])),
            "FOF parser doesnt rename apart sibling binders"
        );
        assert_eq!(
            parse("![X]: ?[X]: p(X)"),
            Ok(forall("X", exists("X_1", pred("p", vec![var("X_1")])))),
            "FOF parser doesnt resolve shadowing binders to the innermost one"
        );
    }

    #[test]
    fn test_terms_and_symbols() {
        let (φ, symbols) = fof_formula("![X]: (p(f(X, a), b) & q)").unwrap().1;
        assert_eq!(
            φ,
            forall(
                "X",
                Conjunction(vec![
                    pred(
                        "p",
                        vec![
                            FolTerm::make_multiarg_app(
                                "f",
                                &[var("X"), var("a")]
                            ),
                            var("b"),
                        ]
                    ),
                    atom("q"),
                ])
            ),
            "FOF parser doesnt curry function applications"
        );
        assert_eq!(
            symbols,
            Symbols {
                functions: BTreeMap::from([
                    ("f".to_string(), 2),
                    ("a".to_string(), 0),
                    ("b".to_string(), 0),
                ]),
                predicates: BTreeMap::from([
                    ("p".to_string(), 2),
                    ("q".to_string(), 0),
                ]),
            },
            "FOF parser doesnt collect symbols with their arities"
        );
        assert!(
            fof_formula("![X]: p(X) = X")
                .unwrap()
                .1
                 .1
                .predicates
                .is_empty(),
            "Equality shouldnt be collected as a predicate symbol"
        );
    }

    #[test]
    fn test_equality() {
        assert_eq!(
            parse("![X]: f(X) = X"),
            Ok(forall(
                "X",
                pred(
                    "=",
                    vec![
                        FolTerm::make_multiarg_app("f", &[var("X")]),
                        var("X")
                    ]
                )
            ))
        );
        assert_eq!(
            parse("a != b"),
            Ok(not(pred("=", vec![var("a"), var("b")])))
        );
        assert_eq!(
            parse("$true | $false"),
            Ok(Disjunction(vec![atom("$true"), atom("$false")]))
        );
    }

    #[test]
    fn test_typed_binders() {
        let nat = || Box::new(atom("nat"));
        assert_eq!(
            tff_formula("![X: nat, Y]: ?[Z: nat]: p(X, Y, Z)")
                .map(|(rest, (φ, _))| (rest, φ)),
            Ok((
                "",
                ForAll(
                    "X".to_string(),
                    nat(),
                    Box::new(forall(
                        "Y",
                        Exist(
                            "Z".to_string(),
                            nat(),
                            Box::new(pred(
                                "p",
                                vec![var("X"), var("Y"), var("Z")]
                            ))
                        )
                    ))
                )
            )),
            "TFF parser doesnt type binders, or doesnt default untyped ones to $i"
        );
        assert!(
            fof_formula("![X: nat]: p(X)").is_err(),
            "FOF parser accepts typed binders"
        );
        assert!(
            tff_formula("![X: $o]: X").is_err(),
            "TFF parser accepts variables over formulas (TXF)"
        );
    }
}
