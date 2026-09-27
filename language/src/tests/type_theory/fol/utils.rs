#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use crate::type_theory::{
        fol::fol_utils::clausify,
        grammars::{
            cnf::{CnfFormula, CnfTerm},
            fol::{
                FolFormula::{
                    Arrow, Conjunction, Disjunction, Exist, ForAll, Not,
                    Predicate,
                },
                FolTerm::Variable,
            },
        },
    };

    #[test]
    fn test_clausification() {
        let nat = Predicate("Nat".to_string(), vec![]);
        let no_constants = HashSet::new();

        assert_eq!(
            clausify(
                &ForAll(
                    "x".to_string(),
                    Box::new(nat.clone()),
                    Box::new(Exist(
                        "y".to_string(),
                        Box::new(nat.clone()),
                        Box::new(Disjunction(vec![
                            Predicate(
                                "P".to_string(),
                                vec![Variable("y".to_string())]
                            ),
                            Not(Box::new(Conjunction(vec![
                                Predicate("A".to_string(), vec![]),
                                Predicate("B".to_string(), vec![])
                            ])))
                        ]))
                    ))
                ),
                &no_constants
            ),
            Ok(vec![CnfFormula::Clause(vec![
                CnfFormula::Atom(
                    "P".to_string(),
                    vec![CnfTerm::Application(
                        "sw_0".to_string(),
                        vec![CnfTerm::Variable("x".to_string())],
                    )]
                ),
                CnfFormula::Not(Box::new(CnfFormula::Atom(
                    "A".to_string(),
                    vec![]
                ))),
                CnfFormula::Not(Box::new(CnfFormula::Atom(
                    "B".to_string(),
                    vec![]
                ))),
            ])]),
            "Clausification didnt produce the expected formula"
        );

        assert_eq!(
            clausify(
                &Arrow(
                    Box::new(Conjunction(vec![
                        Predicate("A".to_string(), vec![]),
                        Predicate("B".to_string(), vec![]),
                    ])),
                    Box::new(Predicate("H".to_string(), vec![])),
                ),
                &no_constants
            ),
            Ok(vec![CnfFormula::Clause(vec![
                CnfFormula::Not(Box::new(CnfFormula::Atom(
                    "A".to_string(),
                    vec![]
                ))),
                CnfFormula::Not(Box::new(CnfFormula::Atom(
                    "B".to_string(),
                    vec![]
                ))),
                CnfFormula::Atom("H".to_string(), vec![]),
            ])]),
            "A rule with a 2-literal conjunctive body (H :- A, B) must clausify to the single Horn clause ¬A∨¬B∨H, not two separate (and logically weaker) clauses"
        );
    }

    #[test]
    fn test_equality_clausification() {
        let constants = HashSet::from(["a".to_string()]);
        // ∀x. x = a ∨ ¬(a = x)
        assert_eq!(
            clausify(
                &ForAll(
                    "x".to_string(),
                    Box::new(Predicate("$i".to_string(), vec![])),
                    Box::new(Disjunction(vec![
                        Predicate(
                            "=".to_string(),
                            vec![
                                Variable("x".to_string()),
                                Variable("a".to_string())
                            ]
                        ),
                        Not(Box::new(Predicate(
                            "=".to_string(),
                            vec![
                                Variable("a".to_string()),
                                Variable("x".to_string())
                            ]
                        ))),
                    ])),
                ),
                &constants
            ),
            Ok(vec![CnfFormula::Clause(vec![
                CnfFormula::Equality(
                    CnfTerm::Variable("x".to_string()),
                    CnfTerm::Application("a".to_string(), vec![])
                ),
                CnfFormula::Not(Box::new(CnfFormula::Equality(
                    CnfTerm::Application("a".to_string(), vec![]),
                    CnfTerm::Variable("x".to_string())
                ))),
            ])]),
            "Clausification doesnt map the `=` predicate to CNF equality"
        );
    }
}
