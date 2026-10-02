#[cfg(test)]
mod unit_tests {
    use crate::{
        error::LofError,
        tptp::prp::prp_formula,
        type_theory::grammars::prop::PropFormula::{
            self, Arrow, Atom, Conjunction, Disjunction, Not,
        },
    };

    /// Parses `input` expecting it to be entirely consumed
    fn parse(input: &str) -> Result<PropFormula, LofError> {
        match prp_formula(input) {
            Ok(("", φ)) => Ok(φ),
            Ok((rest, _)) => {
                Err(LofError::custom(format!("leftover: {}", rest)))
            }
            Err(err) => Err(err.into()),
        }
    }

    fn atom(name: &str) -> PropFormula {
        Atom(name.to_string())
    }
    fn not(φ: PropFormula) -> PropFormula {
        Not(Box::new(φ))
    }
    fn arrow(l: PropFormula, r: PropFormula) -> PropFormula {
        Arrow(Box::new(l), Box::new(r))
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
            "Disjunction chains arent flattened"
        );
        assert_eq!(
            parse("p & (q | r) & s"),
            Ok(Conjunction(vec![
                atom("p"),
                Disjunction(vec![atom("q"), atom("r")]),
                atom("s"),
            ])),
            "Conjunction chains arent flattened"
        );
        assert!(
            parse("p | q & r").is_err(),
            "Mixed connectives without parentheses are accepted"
        );
        assert!(
            parse("p => q => r").is_err(),
            "Chained non associative connectives are accepted"
        );
    }

    #[test]
    fn test_atoms_and_constants() {
        assert_eq!(parse("~ ~ p"), Ok(not(not(atom("p")))));
        assert_eq!(
            parse("$true | $false"),
            Ok(Disjunction(vec![Conjunction(vec![]), Disjunction(vec![])])),
            "Truth constants arent the empty conjunction and disjunction"
        );
        assert_eq!(
            parse("'It rains' => 'abc'"),
            Ok(arrow(atom("It rains"), atom("abc")))
        );
    }

    #[test]
    fn test_first_order_constructs() {
        for first_order in [
            "![X]: p",
            "? [X] : p",
            "X",
            "p(a)",
            "a = b",
            "a != b",
            "$distinct",
        ] {
            assert!(
                parse(first_order).is_err(),
                "First order formula `{}` is accepted as propositional",
                first_order
            );
        }
    }
}
