#[cfg(test)]
mod unit_tests {
    use crate::{
        tptp::{
            header::{Form, Order, Status},
            problem::{parse_tptp, TptpBody, TptpInput},
            syntax::Role,
        },
        type_theory::grammars::prop::PropFormula::{Arrow, Atom},
    };

    /// A problem with the given `% SPC` and status, and `body` as formulas
    fn problem(status: &str, spc: &str, body: &str) -> String {
        format!("% Status   : {}\n% SPC      : {}\n{}", status, spc, body)
    }

    #[test]
    fn test_propositional_problem() {
        let problem = parse_tptp(&problem(
            "Theorem",
            "FOF_THM_PRP",
            "fof(ax, axiom, p => q, file('a.p', ax)).
            fof(1, conjecture, p).",
        ))
        .unwrap();

        assert_eq!(problem.header.status, Status::Theorem);
        assert_eq!(problem.header.form, Form::Fof);
        assert_eq!(problem.header.order, Some(Order::Propositional));
        assert_eq!(
            problem.body,
            TptpBody::Propositional(vec![
                TptpInput {
                    name: "ax".to_string(),
                    role: Role::Axiom,
                    formula: Arrow(
                        Box::new(Atom("p".to_string())),
                        Box::new(Atom("q".to_string()))
                    ),
                },
                TptpInput {
                    name: "1".to_string(),
                    role: Role::Conjecture,
                    formula: Atom("p".to_string()),
                },
            ]),
            "Propositional problems arent parsed to propositional formulas"
        );
    }

    #[test]
    fn test_header_decides_the_logic() {
        assert!(
            parse_tptp("fof(a, axiom, p).").is_err(),
            "Problems without a header are accepted"
        );
        assert!(
            parse_tptp(&problem(
                "Theorem",
                "FOF_THM_RFO_NEQ",
                "fof(a, conjecture, p)."
            ))
            .is_err(),
            "First order problems are parsed as propositional"
        );
        assert!(
            parse_tptp(&problem(
                "Unsatisfiable",
                "CNF_UNS_PRP",
                "cnf(a, axiom, p)."
            ))
            .is_err(),
            "Propositional CNF problems are accepted before being supported"
        );
        assert!(
            parse_tptp(&problem(
                "Theorem",
                "FOF_THM_PRP",
                "fof(a, axiom, p(X))."
            ))
            .is_err(),
            "Propositional problems with first order formulas are accepted"
        );
    }

    #[test]
    fn test_annotated_formulas_follow_the_header() {
        assert!(
            parse_tptp(&problem(
                "Satisfiable",
                "FOF_SAT_PRP",
                "cnf(a, axiom, p)."
            ))
            .is_err(),
            "`cnf` formulas are accepted in a FOF problem"
        );
        assert!(
            parse_tptp(&problem(
                "Satisfiable",
                "FOF_SAT_PRP",
                "include('Axioms/PRP001+0.ax')."
            ))
            .is_err(),
            "Include directives are accepted before being supported"
        );
        assert!(
            parse_tptp(&problem(
                "Satisfiable",
                "FOF_SAT_PRP",
                "fof(a, axiom, p) fof(b, axiom, q)."
            ))
            .is_err(),
            "Annotated formulas not terminated by a dot are accepted"
        );
        assert_eq!(
            parse_tptp(&problem("Satisfiable", "FOF_SAT_PRP", ""))
                .map(|p| p.body),
            Ok(TptpBody::Propositional(vec![])),
            "Problems with no formulas arent accepted"
        );
    }
}
