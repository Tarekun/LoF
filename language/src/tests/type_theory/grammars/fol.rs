use crate::type_theory::grammars::{
    fol::{
        FolFormula::{
            self, Arrow, Conjunction, Disjunction, Exist, ForAll, Not,
            Predicate,
        },
        FolTerm::{self, Abstraction, Application, Let, Tuple, Variable},
    },
    traits::NamedSubstitution,
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
            Box::new(Predicate("Nat".to_string(), vec![])),
            Box::new(Predicate("A".to_string(), vec![]))
        )))
        .negation_normal_form(),
        ForAll(
            "x".to_string(),
            Box::new(Predicate("Nat".to_string(), vec![])),
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
                    Box::new(Predicate("P".to_string(), vec![]))
                ))
            ),
            Predicate("Q".to_string(), vec![])
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
                    vec![Variable("n".to_string()), Variable("m".to_string())]
                ))
            ))
        )
        .skolemize(),
        Predicate(
            "P".to_string(),
            vec![Variable("sw_0".to_string()), Variable("sw_1".to_string())]
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

fn var(name: &str) -> FolTerm {
    Variable(name.to_string())
}
fn app(fun: FolTerm, arg: FolTerm) -> FolTerm {
    Application(Box::new(fun), Box::new(arg))
}
fn pred(name: &str, args: Vec<FolTerm>) -> FolFormula {
    Predicate(name.to_string(), args)
}
fn not(φ: FolFormula) -> FolFormula {
    Not(Box::new(φ))
}
fn arrow(assumption: FolFormula, conclusion: FolFormula) -> FolFormula {
    Arrow(Box::new(assumption), Box::new(conclusion))
}
fn forall(
    var_name: &str,
    var_type: FolFormula,
    body: FolFormula,
) -> FolFormula {
    ForAll(var_name.to_string(), Box::new(var_type), Box::new(body))
}
fn exist(var_name: &str, var_type: FolFormula, body: FolFormula) -> FolFormula {
    Exist(var_name.to_string(), Box::new(var_type), Box::new(body))
}

#[test]
fn test_rendering() {
    let (a, b, nat) =
        (pred("A", vec![]), pred("B", vec![]), pred("Nat", vec![]));
    let cases = vec![
        (
            pred("P", vec![var("x")]),
            "P([Variable(\"x\")])",
            "P([Variable(\"x\")])",
        ),
        (not(a.clone()), "¬A([])", "¬(A([]))"),
        (
            arrow(a.clone(), b.clone()),
            "A([]) → B([])",
            "(A([]) → B([]))",
        ),
        (
            Conjunction(vec![a.clone(), b.clone()]),
            "A([])∧B([])",
            "(A([])∧B([]))",
        ),
        (
            Disjunction(vec![a.clone(), b.clone()]),
            "A([])∨B([])",
            "(A([])∨B([]))",
        ),
        (
            forall("x", nat.clone(), a.clone()),
            "∀x:Nat([]). A([])",
            "∀x:Nat([]). (A([]))",
        ),
        (
            exist("x", nat.clone(), a.clone()),
            "∃x:Nat([]). A([])",
            "∃x:Nat([]). (A([]))",
        ),
    ];

    for (formula, displayed, debugged) in cases {
        assert_eq!(
            format!("{}", formula),
            displayed,
            "Wrong Display rendering"
        );
        assert_eq!(format!("{:?}", formula), debugged, "Wrong Debug rendering");
    }
}

#[test]
fn test_application_components() {
    let (f, a, b) = (var("f"), var("a"), var("b"));

    assert_eq!(
        app(app(f.clone(), a.clone()), b.clone()).get_application_components(),
        Ok(("f".to_string(), vec![a.clone(), b.clone()])),
        "Curried application isnt split into function name and ordered arguments"
    );
    assert_eq!(
        f.get_application_components(),
        Ok(("f".to_string(), vec![])),
        "Variable isnt treated as a nullary application"
    );
    assert_eq!(
        Abstraction(
            "x".to_string(),
            Box::new(pred("Nat", vec![])),
            Box::new(a.clone())
        )
        .get_application_components(),
        Ok(("".to_string(), vec![])),
        "Abstraction isnt treated as an anonymous nullary application"
    );
    assert!(
        Tuple(vec![a.clone()]).get_application_components().is_err(),
        "Tuple is accepted as an application"
    );
    assert!(
        app(Tuple(vec![]), a.clone())
            .get_application_components()
            .is_err(),
        "Application of a tuple is accepted as an application"
    );
}

#[test]
fn test_make_multiarg_app() {
    assert_eq!(
        FolTerm::make_multiarg_app("f", &[]),
        var("f"),
        "Nullary application isnt the function variable itself"
    );
    assert_eq!(
        FolTerm::make_multiarg_app("f", &[var("a"), var("b")]),
        app(app(var("f"), var("a")), var("b")),
        "Arguments arent applied left to right in curried form"
    );
}

/// Returns `term` where each instance of `target_name` is substituted with `arg`
fn substituted<A, T: NamedSubstitution<A>>(
    mut term: T,
    target_name: &str,
    arg: &A,
) -> T {
    term.substitute_name(target_name, arg);
    term
}

#[test]
fn test_term_substitution() {
    let (x, k) = (var("x"), var("k"));
    let nat_of = |t: &FolTerm| pred("Nat", vec![t.clone()]);
    let let_term = |name: &str,
                    var_type: Option<FolFormula>,
                    t: &FolTerm,
                    scope: &FolTerm| {
        Let(
            name.to_string(),
            Box::new(var_type),
            Box::new(t.clone()),
            Box::new(scope.clone()),
        )
    };

    assert_eq!(
        substituted(x.clone(), "x", &k),
        k,
        "Target variable isnt substituted"
    );
    assert_eq!(
        substituted(var("y"), "x", &k),
        var("y"),
        "Other variable is substituted"
    );
    assert_eq!(
        substituted(app(x.clone(), Tuple(vec![x.clone(), var("y")])), "x", &k),
        app(k.clone(), Tuple(vec![k.clone(), var("y")])),
        "Substitution doesnt reach applications and tuples"
    );
    assert_eq!(
        substituted(
            Abstraction(
                "y".to_string(),
                Box::new(nat_of(&x)),
                Box::new(x.clone())
            ),
            "x",
            &k
        ),
        Abstraction("y".to_string(), Box::new(nat_of(&k)), Box::new(k.clone())),
        "Substitution doesnt reach abstraction type and body"
    );
    let shadowing =
        Abstraction("x".to_string(), Box::new(nat_of(&x)), Box::new(x.clone()));
    assert_eq!(
        substituted(shadowing.clone(), "x", &k),
        shadowing,
        "Substitution goes through an abstraction binding the same name"
    );
    assert_eq!(
        substituted(let_term("y", Some(nat_of(&x)), &x, &x), "x", &k),
        let_term("y", Some(nat_of(&k)), &k, &k),
        "Substitution doesnt reach let type, body and scope"
    );
    assert_eq!(
        substituted(let_term("y", None, &x, &x), "x", &k),
        let_term("y", None, &k, &k),
        "Substitution breaks untyped let definitions"
    );
    assert_eq!(
        substituted(let_term("x", None, &x, &x), "x", &k),
        let_term("x", None, &k, &x),
        "Substitution goes through the scope of a let binding the same name"
    );
}

#[test]
fn test_formula_substitution() {
    let (x, k) = (var("x"), var("k"));
    let nat = pred("Nat", vec![]);
    let body = |t: &FolTerm| {
        Conjunction(vec![
            arrow(pred("P", vec![t.clone()]), not(pred("Q", vec![t.clone()]))),
            Disjunction(vec![pred("R", vec![t.clone()])]),
        ])
    };

    assert_eq!(
        substituted(body(&x), "x", &k),
        body(&k),
        "Substitution doesnt reach every connective"
    );
    for quantify in [forall, exist] {
        assert_eq!(
            substituted(
                quantify("y", pred("Vec", vec![x.clone()]), body(&x)),
                "x",
                &k
            ),
            quantify("y", pred("Vec", vec![k.clone()]), body(&k)),
            "Substitution doesnt reach quantifier type and body"
        );
        let shadowing = quantify("x", nat.clone(), body(&x));
        assert_eq!(
            substituted(shadowing.clone(), "x", &k),
            shadowing,
            "Substitution goes through a quantifier binding the same name"
        );
    }
}

#[test]
fn test_swap_binded_formula() {
    let nat = pred("Nat", vec![]);
    let (old_body, new_body) = (pred("P", vec![]), pred("Q", vec![]));

    assert_eq!(
        forall("x", nat.clone(), exist("y", nat.clone(), old_body.clone()))
            .swap_binded_formula(&new_body),
        forall("x", nat.clone(), exist("y", nat.clone(), new_body.clone())),
        "Quantifier prefix isnt kept while swapping its body"
    );
    assert_eq!(
        old_body.swap_binded_formula(&new_body),
        new_body,
        "Unquantified formula isnt replaced by the new body"
    );
}

#[test]
fn test_negation_normal_form_positive_polarity() {
    let (a, b, nat) =
        (pred("A", vec![]), pred("B", vec![]), pred("Nat", vec![]));
    let (not_a, not_b) = (not(a.clone()), not(b.clone()));

    assert_eq!(
        Conjunction(vec![a.clone(), not_b.clone()]).negation_normal_form(),
        Conjunction(vec![a.clone(), not_b.clone()]),
        "NNF algorithm alters a conjunction already in NNF"
    );
    assert_eq!(
        Disjunction(vec![not_a.clone(), b.clone()]).negation_normal_form(),
        Disjunction(vec![not_a.clone(), b.clone()]),
        "NNF algorithm alters a disjunction already in NNF"
    );
    assert_eq!(
        not(Disjunction(vec![a.clone(), b.clone()])).negation_normal_form(),
        Conjunction(vec![not_a.clone(), not_b.clone()]),
        "NNF algorithm doesnt apply simple De Morgan on disjunctions"
    );
    assert_eq!(
        forall("x", nat.clone(), a.clone()).negation_normal_form(),
        forall("x", nat.clone(), a.clone()),
        "NNF algorithm alters a universal quantifier"
    );
    assert_eq!(
        exist("x", nat.clone(), a.clone()).negation_normal_form(),
        exist("x", nat.clone(), a.clone()),
        "NNF algorithm alters an existential quantifier"
    );
}

#[test]
fn test_prenex_normal_form_implications() {
    let (p, q, nat) =
        (pred("P", vec![]), pred("Q", vec![]), pred("Nat", vec![]));

    assert_eq!(
        arrow(forall("x", nat.clone(), p.clone()), q.clone())
            .prenex_normal_form(),
        exist("x", nat.clone(), arrow(p.clone(), q.clone())),
        "PNF algorithm doesnt turn a universal assumption into an existential"
    );
    assert_eq!(
        arrow(exist("x", nat.clone(), p.clone()), q.clone())
            .prenex_normal_form(),
        forall("x", nat.clone(), arrow(p.clone(), q.clone())),
        "PNF algorithm doesnt turn an existential assumption into a universal"
    );
}

#[test]
fn test_skolemization_through_connectives() {
    let nat = pred("Nat", vec![]);
    let pn = pred("P", vec![var("n")]);
    let witness = pred("P", vec![var("sw_0")]);

    assert_eq!(
        exist(
            "n",
            nat.clone(),
            Conjunction(vec![
                Disjunction(vec![pn.clone(), not(pn.clone())]),
                arrow(pn.clone(), pn.clone()),
            ])
        )
        .skolemize(),
        Conjunction(vec![
            Disjunction(vec![witness.clone(), not(witness.clone())]),
            arrow(witness.clone(), witness.clone()),
        ]),
        "Skolem witness doesnt replace the variable under every connective"
    );
}

#[test]
fn test_conjunction_normal_form_flattens_long_disjunctions() {
    let (a, b, c) = (pred("A", vec![]), pred("B", vec![]), pred("C", vec![]));

    assert_eq!(
        Disjunction(vec![a.clone(), b.clone(), c.clone()])
            .conjunction_normal_form(),
        vec![Disjunction(vec![a, b, c])],
        "CNF algorithm nests disjunctions of more than two literals"
    );
}

#[test]
#[should_panic(
    expected = "Existential quantifiers should be removed by skolemization"
)]
fn test_conjunction_normal_form_rejects_existentials() {
    exist("x", pred("Nat", vec![]), pred("P", vec![]))
        .conjunction_normal_form();
}

#[test]
#[should_panic(
    expected = "Implications should be removed by negation normal form"
)]
fn test_conjunction_normal_form_rejects_implications() {
    arrow(pred("P", vec![]), pred("Q", vec![])).conjunction_normal_form();
}
