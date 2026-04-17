#[cfg(test)]
mod tests {
    use crate::type_theory::{
        fol::{
            fol::{
                FolFormula::{
                    Arrow, Conjunction, Disjunction, Exist, ForAll, Not,
                    Predicate,
                },
                FolTerm::{Application, Variable},
            },
            fol_utils::{
                clausify, conjunction_normal_form, negation_normal_form,
                prenex_normal_form, skolemize,
            },
        },
        sup::sup::{SupFormula, SupTerm},
    };

    #[test]
    fn test_negation_normal_form() {
        assert_eq!(
            negation_normal_form(&Not(Box::new(Conjunction(vec![
                Predicate("A".to_string(), vec![]),
                Predicate("B".to_string(), vec![])
            ])))),
            Disjunction(vec![
                Not(Box::new(Predicate("A".to_string(), vec![]))),
                Not(Box::new(Predicate("B".to_string(), vec![]))),
            ]),
            "NNF algorithm doesnt apply simple De Morgan on conjunctions"
        );

        assert_eq!(
            negation_normal_form(&Arrow(
                Box::new(Predicate("A".to_string(), vec![])),
                Box::new(Predicate("B".to_string(), vec![])),
            )),
            Disjunction(vec![
                Not(Box::new(Predicate("A".to_string(), vec![]))),
                Predicate("B".to_string(), vec![]),
            ]),
            "NNF algorithm doesnt resolve implications"
        );

        assert_eq!(
            negation_normal_form(&Not(Box::new(Not(Box::new(Predicate(
                "A".to_string(),
                vec![]
            )))))),
            Predicate("A".to_string(), vec![]),
            "NNF algorithm doesnt resolve double negation"
        );

        assert_eq!(
            negation_normal_form(&Not(Box::new(ForAll(
                "x".to_string(),
                Box::new(Predicate("Nat".to_string(), vec![])),
                Box::new(Predicate("A".to_string(), vec![]))
            )))),
            Exist(
                "x".to_string(),
                Box::new(Predicate("Nat".to_string(), vec![])),
                Box::new(Not(Box::new(Predicate("A".to_string(), vec![]))))
            ),
            "NNF algorithm doesnt push down negation over universal quantifier"
        );
        assert_eq!(
            negation_normal_form(&Not(Box::new(Exist(
                "x".to_string(),
                Box::new(Predicate("Nat".to_string(),vec![])),
                Box::new(Predicate("A".to_string(), vec![]))
            )))),
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
            prenex_normal_form(&Conjunction(vec![
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
            ])),
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
            prenex_normal_form(&Disjunction(vec![
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
            ])),
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
            prenex_normal_form(&Conjunction(vec![
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
            ])),
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
            conjunction_normal_form(&Disjunction(vec![
                Predicate("A".to_string(), vec![]),
                Conjunction(vec![
                    Predicate("B".to_string(), vec![]),
                    Predicate("C".to_string(), vec![]),
                ])
            ])),
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
            conjunction_normal_form(&Disjunction(vec![
                Conjunction(vec![
                    Predicate("B".to_string(), vec![]),
                    Predicate("C".to_string(), vec![]),
                ]),
                Predicate("A".to_string(), vec![]),
            ])),
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
            conjunction_normal_form(&Disjunction(vec![
                Conjunction(vec![
                    Predicate("A".to_string(), vec![]),
                    Predicate("B".to_string(), vec![]),
                ]),
                Conjunction(vec![
                    Predicate("C".to_string(), vec![]),
                    Predicate("D".to_string(), vec![]),
                ]),
            ])),
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
            conjunction_normal_form(&ForAll(
                "n".to_string(),
                Box::new(Predicate("Nat".to_string(), vec![])),
                Box::new(Conjunction(vec![
                    Predicate("P".to_string(), vec![]),
                    Predicate("Q".to_string(), vec![])
                ]))
            )),
            vec![
                Predicate("P".to_string(), vec![]),
                Predicate("Q".to_string(), vec![]),
            ],
            "CNF algorithm isnt dropping universal quantifier"
        );

        assert_eq!(
            conjunction_normal_form(&Disjunction(vec![
                Predicate("A".to_string(), vec![]),
                Conjunction(vec![
                    Predicate("B".to_string(), vec![]),
                    Disjunction(vec![
                        Predicate("C".to_string(), vec![]),
                        Predicate("D".to_string(), vec![]),
                    ])
                ])
            ])),
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
            skolemize(&Exist(
                "n".to_string(),
                Box::new(Predicate("Nat".to_string(), vec![])),
                Box::new(Predicate(
                    "P".to_string(),
                    vec![Variable("n".to_string())]
                ))
            )),
            Predicate("P".to_string(), vec![Variable("sw_0".to_string())]),
            "Skolemization algorithm doesnt remove one single existential"
        );

        assert_eq!(
            skolemize(&Exist(
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
            )),
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
            skolemize(&ForAll(
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
            )),
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

        assert_eq!(
            clausify(&ForAll(
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
            )),
            Ok(vec![SupFormula::Clause(vec![
                SupFormula::Atom(
                    "P".to_string(),
                    vec![SupTerm::Application(
                        "sw_0".to_string(),
                        vec![SupTerm::Variable("x".to_string())],
                    )]
                ),
                SupFormula::Not(Box::new(SupFormula::Atom(
                    "A".to_string(),
                    vec![]
                ))),
                SupFormula::Not(Box::new(SupFormula::Atom(
                    "B".to_string(),
                    vec![]
                ))),
            ])]),
            "Clausification didnt produce the expected formula"
        );
    }
}
