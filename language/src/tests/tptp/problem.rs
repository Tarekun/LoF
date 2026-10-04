#[cfg(test)]
mod unit_tests {
    use crate::{
        tptp::{
            header::{Form, Order, Status},
            problem::{parse_tptp, TptpBody, TptpInput},
            syntax::Role,
            thf::ThfInput,
        },
        type_theory::grammars::{
            cnf::{CnfFormula, CnfTerm},
            prop::PropFormula::{Arrow, Atom},
        },
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
    fn test_clausal_problem() {
        let clausal = parse_tptp(&problem(
            "Unsatisfiable",
            "CNF_UNS_EPR_NEQ_HRN",
            "cnf(a, axiom, p(X)).
            cnf(b, negated_conjecture, ~ p(a)).",
        ))
        .unwrap();

        assert_eq!(
            clausal.body,
            TptpBody::Clausal(vec![
                TptpInput {
                    name: "a".to_string(),
                    role: Role::Axiom,
                    formula: CnfFormula::Atom(
                        "p".to_string(),
                        vec![CnfTerm::Variable("X".to_string())]
                    ),
                },
                TptpInput {
                    name: "b".to_string(),
                    role: Role::NegatedConjecture,
                    formula: CnfFormula::Not(Box::new(CnfFormula::Atom(
                        "p".to_string(),
                        vec![CnfTerm::Application("a".to_string(), vec![])]
                    ))),
                },
            ]),
            "First order CNF problems arent parsed to CNF clauses"
        );
        assert!(
            parse_tptp(&problem(
                "Unsatisfiable",
                "CNF_UNS_RFO_NEQ_HRN",
                "fof(a, axiom, p)."
            ))
            .is_err(),
            "`fof` formulas are accepted in a CNF problem"
        );
    }

    #[test]
    fn test_higher_order_problem() {
        let higher_order = parse_tptp(&problem(
            "Theorem",
            "TH0_THM_NEQ_NAR",
            "thf(p_decl, type, p: $o).
            thf(excluded_middle, conjecture, p | ~ p).",
        ))
        .unwrap();
        let TptpBody::HigherOrder(inputs) = higher_order.body else {
            panic!("TH0 problems arent parsed as higher order ones")
        };
        assert_eq!(
            inputs.iter().map(|input| &input.name).collect::<Vec<_>>(),
            vec!["p_decl", "excluded_middle"]
        );
        assert!(
            matches!(inputs[0].formula, ThfInput::Declaration(..))
                && matches!(inputs[1].formula, ThfInput::Formula(..)),
            "THF type declarations and formulas arent told apart"
        );
        assert!(
            parse_tptp(&problem(
                "Theorem",
                "TH1_THM_NEQ_NAR",
                "fof(a, conjecture, p)."
            ))
            .is_err(),
            "`fof` formulas are accepted in a THF problem"
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
        assert_eq!(
            parse_tptp(&problem(
                "Unsatisfiable",
                "CNF_UNS_PRP",
                "cnf(a, axiom, p)."
            ))
            .map(|p| p.body),
            Ok(TptpBody::Clausal(vec![TptpInput {
                name: "a".to_string(),
                role: Role::Axiom,
                formula: CnfFormula::Atom("p".to_string(), vec![]),
            }])),
            "Propositional CNF problems arent parsed to nullary CNF atoms"
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
                "include('Axioms/missing.ax')."
            ))
            .is_err(),
            "Includes of missing files are accepted"
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
