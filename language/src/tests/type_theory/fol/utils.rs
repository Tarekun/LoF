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
                FolTerm::{Application, Variable},
            },
        },
    };

    #[test]
    fn test_negation_normal_form() {
        assert_eq!(
            Not(Box::new(Conjunction(vec![
                Predicate("A".to_string(), vec![]),
                Predicate("B".to_string(), vec![])
            ])))
            .negation_normal_form(),
            Disjunction(vec![
                Not(Box::new(Predicate("A".to_string(), vec![]))),
                Not(Box::new(Predicate("B".to_string(), vec![]))),
            ]),
            "NNF algorithm doesnt apply simple De Morgan on conjunctions"
        );

        assert_eq!(
            Arrow(
                Box::new(Predicate("A".to_string(), vec![])),
                Box::new(Predicate("B".to_string(), vec![])),
            )
            .negation_normal_form(),
            Disjunction(vec![
                Not(Box::new(Predicate("A".to_string(), vec![]))),
                Predicate("B".to_string(), vec![]),
            ]),
            "NNF algorithm doesnt resolve implications"
        );

        assert_eq!(
            Arrow(
                Box::new(Conjunction(vec![
                    Predicate("A".to_string(), vec![]),
                    Predicate("B".to_string(), vec![]),
                ])),
                Box::new(Predicate("H".to_string(), vec![])),
            ).negation_normal_form(),
            Disjunction(vec![
                Disjunction(vec![
                    Not(Box::new(Predicate("A".to_string(), vec![]))),
                    Not(Box::new(Predicate("B".to_string(), vec![]))),
                ]),
                Predicate("H".to_string(), vec![]),
            ]),
            "NNF algorithm doesnt apply De Morgan when negation reaches a conjunction through an implication's antecedent (not just through a literal ¬ node)"
        );

        assert_eq!(
            Not(Box::new(Not(Box::new(Predicate("A".to_string(), vec![])))))
                .negation_normal_form(),
            Predicate("A".to_string(), vec![]),
            "NNF algorithm doesnt resolve double negation"
        );

        assert_eq!(
            Not(Box::new(ForAll(
                "x".to_string(),
                Box::new(Predicate("Nat".to_string(), vec![])),
                Box::new(Predicate("A".to_string(), vec![]))
            )))
            .negation_normal_form(),
            Exist(
                "x".to_string(),
                Box::new(Predicate("Nat".to_string(), vec![])),
                Box::new(Not(Box::new(Predicate("A".to_string(), vec![]))))
            ),
            "NNF algorithm doesnt push down negation over universal quantifier"
        );
        assert_eq!(
            Not(Box::new(Exist(
                "x".to_string(),
                Box::new(Predicate("Nat".to_string(),vec![])),
                Box::new(Predicate("A".to_string(), vec![]))
            ))).negation_normal_form(),
            ForAll(
                "x".to_string(),
                Box::new(Predicate("Nat".to_string(),vec![])),
                Box::new(Not(Box::new(Predicate("A".to_string(), vec![]))))
            ),
            "NNF algorithm doesnt push down negation over existential quantifier"
        );
    }

    #[test]
    fn test_prenex_normal_form() {
        assert_eq!(
            Conjunction(vec![
                ForAll(
                    "a".to_string(),
                    Box::new(Predicate("A".to_string(), vec![])),
                    Box::new(Predicate("P".to_string(), vec![]))
                ),
                Exist(
                    "b".to_string(),
                    Box::new(Predicate("B".to_string(), vec![])),
                    Box::new(Predicate("Q".to_string(), vec![]))
                ),
            ])
            .prenex_normal_form(),
            ForAll(
                "a".to_string(),
                Box::new(Predicate("A".to_string(), vec![])),
                Box::new(Exist(
                    "b".to_string(),
                    Box::new(Predicate("B".to_string(), vec![])),
                    Box::new(Conjunction(vec![
                        Predicate("P".to_string(), vec![]),
                        Predicate("Q".to_string(), vec![])
                    ]))
                ))
            ),
            "PNF algorithm couldnt pull out quantifiers in conjunctions"
        );

        assert_eq!(
            Disjunction(vec![
                Exist(
                    "a".to_string(),
                    Box::new(Predicate("A".to_string(), vec![])),
                    Box::new(Predicate("P".to_string(), vec![]))
                ),
                ForAll(
                    "b".to_string(),
                    Box::new(Predicate("B".to_string(), vec![])),
                    Box::new(Predicate("Q".to_string(), vec![]))
                ),
            ])
            .prenex_normal_form(),
            Exist(
                "a".to_string(),
                Box::new(Predicate("A".to_string(), vec![])),
                Box::new(ForAll(
                    "b".to_string(),
                    Box::new(Predicate("B".to_string(), vec![])),
                    Box::new(Disjunction(vec![
                        Predicate("P".to_string(), vec![]),
                        Predicate("Q".to_string(), vec![])
                    ]))
                ))
            ),
            "PNF algorithm couldnt pull out quantifiers in disjunction"
        );

        assert_eq!(
            Conjunction(vec![
                ForAll(
                    "a".to_string(),
                    Box::new(Predicate("A".to_string(), vec![])),
                    Box::new(Exist(
                        "b".to_string(),
                        Box::new(Predicate("B".to_string(), vec![])),
                        Box::new(Predicate("P".to_string(),vec![]))
                    ))
                ),
                Predicate("Q".to_string(),vec![])
            ]).prenex_normal_form(),
            ForAll(
                "a".to_string(),
                Box::new(Predicate("A".to_string(), vec![])),
                Box::new(Exist(
                    "b".to_string(),
                    Box::new(Predicate("B".to_string(), vec![])),
                    Box::new(Conjunction(vec![
                        Predicate("P".to_string(),vec![]),
                        Predicate("Q".to_string(),vec![])
                    ]))
                ))
            ),
            "PNF algorithm couldnt cope with double quantifiers in a subformula"
        );
    }

    #[test]
    fn test_conjunction_normal_form() {
        assert_eq!(
            Disjunction(vec![
                Predicate("A".to_string(), vec![]),
                Conjunction(vec![
                    Predicate("B".to_string(), vec![]),
                    Predicate("C".to_string(), vec![]),
                ])
            ])
            .conjunction_normal_form(),
            vec![
                Disjunction(vec![
                    Predicate("A".to_string(), vec![]),
                    Predicate("B".to_string(), vec![]),
                ]),
                Disjunction(vec![
                    Predicate("A".to_string(), vec![]),
                    Predicate("C".to_string(), vec![]),
                ]),
            ],
            "CNF isnt distributing a predicate to the right"
        );
        assert_eq!(
            Disjunction(vec![
                Conjunction(vec![
                    Predicate("B".to_string(), vec![]),
                    Predicate("C".to_string(), vec![]),
                ]),
                Predicate("A".to_string(), vec![]),
            ])
            .conjunction_normal_form(),
            vec![
                Disjunction(vec![
                    Predicate("B".to_string(), vec![]),
                    Predicate("A".to_string(), vec![]),
                ]),
                Disjunction(vec![
                    Predicate("C".to_string(), vec![]),
                    Predicate("A".to_string(), vec![]),
                ]),
            ],
            "CNF isnt distributing a predicate to the left"
        );

        assert_eq!(
            Disjunction(vec![
                Conjunction(vec![
                    Predicate("A".to_string(), vec![]),
                    Predicate("B".to_string(), vec![]),
                ]),
                Conjunction(vec![
                    Predicate("C".to_string(), vec![]),
                    Predicate("D".to_string(), vec![]),
                ]),
            ])
            .conjunction_normal_form(),
            vec![
                Disjunction(vec![
                    Predicate("A".to_string(), vec![]),
                    Predicate("C".to_string(), vec![]),
                ]),
                Disjunction(vec![
                    Predicate("A".to_string(), vec![]),
                    Predicate("D".to_string(), vec![]),
                ]),
                Disjunction(vec![
                    Predicate("B".to_string(), vec![]),
                    Predicate("C".to_string(), vec![]),
                ]),
                Disjunction(vec![
                    Predicate("B".to_string(), vec![]),
                    Predicate("D".to_string(), vec![]),
                ]),
            ],
            "CNF doesnt work properly with double distribution"
        );

        assert_eq!(
            ForAll(
                "n".to_string(),
                Box::new(Predicate("Nat".to_string(), vec![])),
                Box::new(Conjunction(vec![
                    Predicate("P".to_string(), vec![]),
                    Predicate("Q".to_string(), vec![])
                ]))
            )
            .conjunction_normal_form(),
            vec![
                Predicate("P".to_string(), vec![]),
                Predicate("Q".to_string(), vec![]),
            ],
            "CNF algorithm isnt dropping universal quantifier"
        );

        assert_eq!(
            Disjunction(vec![
                Predicate("A".to_string(), vec![]),
                Conjunction(vec![
                    Predicate("B".to_string(), vec![]),
                    Disjunction(vec![
                        Predicate("C".to_string(), vec![]),
                        Predicate("D".to_string(), vec![]),
                    ])
                ])
            ])
            .conjunction_normal_form(),
            vec![
                Disjunction(vec![
                    Predicate("A".to_string(), vec![]),
                    Predicate("B".to_string(), vec![]),
                ]),
                Disjunction(vec![
                    Predicate("A".to_string(), vec![]),
                    Predicate("C".to_string(), vec![]),
                    Predicate("D".to_string(), vec![]),
                ])
            ],
            "CNF algorithm isnt producing flattened disjunctions"
        );
    }

    #[test]
    fn test_skolemization() {
        assert_eq!(
            Exist(
                "n".to_string(),
                Box::new(Predicate("Nat".to_string(), vec![])),
                Box::new(Predicate(
                    "P".to_string(),
                    vec![Variable("n".to_string())]
                ))
            )
            .skolemize(),
            Predicate("P".to_string(), vec![Variable("sw_0".to_string())]),
            "Skolemization algorithm doesnt remove one single existential"
        );

        assert_eq!(
            Exist(
                "n".to_string(),
                Box::new(Predicate("Nat".to_string(), vec![])),
                Box::new(Exist(
                    "m".to_string(),
                    Box::new(Predicate("Nat".to_string(), vec![])),
                    Box::new(Predicate(
                        "P".to_string(),
                        vec![
                            Variable("n".to_string()),
                            Variable("m".to_string())
                        ]
                    ))
                ))
            )
            .skolemize(),
            Predicate(
                "P".to_string(),
                vec![
                    Variable("sw_0".to_string()),
                    Variable("sw_1".to_string())
                ]
            ),
            "Skolemization algorithm cant cope with multiple existentials"
        );

        assert_eq!(
            ForAll(
                "x".to_string(),
                Box::new(Predicate("Nat".to_string(), vec![])),
                Box::new(Exist(
                    "n".to_string(),
                    Box::new(Predicate("Nat".to_string(), vec![])),
                    Box::new(Predicate(
                        "P".to_string(),
                        vec![Variable("n".to_string())]
                    ))
                ))
            ).skolemize(),
            ForAll(
                "x".to_string(),
                Box::new(Predicate("Nat".to_string(), vec![])),
                Box::new(Predicate(
                    "P".to_string(),
                    vec![Application(
                        Box::new(Variable("sw_0".to_string())),
                        Box::new(Variable("x".to_string()))
                    )]
                ))
            ),
            "Skolemization algorithm doesnt produce a witness function when nested inside a universal"
        );
    }

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
}
