#[cfg(test)]
mod unit_tests {
    use crate::{
        tptp::cnf::cnf_formula,
        type_theory::grammars::cnf::{
            CnfFormula::{self, Atom, Clause, Equality, Not},
            CnfTerm::{self, Application, Variable},
        },
    };

    fn var(name: &str) -> CnfTerm {
        Variable(name.to_string())
    }
    fn constant(name: &str) -> CnfTerm {
        Application(name.to_string(), vec![])
    }
    fn pred(name: &str, args: Vec<CnfTerm>) -> CnfFormula {
        Atom(name.to_string(), args)
    }
    fn not(φ: CnfFormula) -> CnfFormula {
        Not(Box::new(φ))
    }

    #[test]
    fn test_literals() {
        assert_eq!(
            cnf_formula("p(X, a)"),
            Ok(("", pred("p", vec![var("X"), constant("a")]))),
            "CNF parser doesnt tell variables and constants apart, or doesnt unpack unit clauses"
        );
        assert_eq!(cnf_formula("~ q"), Ok(("", not(pred("q", vec![])))));
        assert_eq!(
            cnf_formula("f(X) = X"),
            Ok((
                "",
                Equality(
                    Application("f".to_string(), vec![var("X")]),
                    var("X")
                )
            ))
        );
        assert_eq!(
            cnf_formula("a != b"),
            Ok(("", not(Equality(constant("a"), constant("b"))))),
            "CNF parser doesnt read disequalities as negated equalities"
        );
    }

    #[test]
    fn test_clauses() {
        let expected = Clause(vec![
            pred("p", vec![var("X")]),
            not(pred("q", vec![var("X")])),
            Equality(var("X"), constant("a")),
        ]);
        assert_eq!(
            cnf_formula("p(X) | ~q(X) | X = a"),
            Ok(("", expected.clone())),
            "CNF parser doesnt handle unparenthesized clauses"
        );
        assert_eq!(
            cnf_formula("( p(X)\n | ~ q(X) % comment\n | X = a )"),
            Ok(("", expected)),
            "CNF parser doesnt handle parenthesized clauses"
        );
    }

    #[test]
    fn test_invalid_clauses() {
        assert!(
            cnf_formula("p & q").map(|(rest, _)| rest) != Ok(""),
            "CNF parser accepts conjunctions"
        );
        assert!(
            cnf_formula("X").is_err(),
            "CNF parser accepts a variable literal"
        );
    }
}
