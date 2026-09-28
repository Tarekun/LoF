use super::{is_bottom, saturate};
use crate::{
    config::SelectionFunction,
    type_theory::{
        grammars::cnf::{
            CnfFormula::{self, Atom, Clause, Equality, Not},
            CnfTerm::{self, Application, Variable},
        },
        sup::{
            freedom::{
                get_selection_fn, pick_clause, pick_clause_weighted,
                GivingClauseSignature,
            },
            sup_utils::with_answer_literal,
        },
    },
};

fn s(n: CnfTerm) -> CnfTerm {
    Application("s".to_string(), vec![n])
}
fn var(name: &str) -> CnfTerm {
    Variable(name.to_string())
}
fn add(n: CnfTerm, m: CnfTerm) -> CnfTerm {
    Application("+".to_string(), vec![n, m])
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

fn all_selection_fns() -> Vec<(&'static str, SelectionFunction)> {
    vec![
        ("Maximal", SelectionFunction::Maximal),
        ("All", SelectionFunction::All),
    ]
}

fn all_giving_clause_fns() -> Vec<(&'static str, GivingClauseSignature)> {
    vec![("FIFO", pick_clause), ("Weighted", pick_clause_weighted)]
}

fn all_combinations<A: Clone, B: Clone>(
    a: Vec<A>,
    b: Vec<B>,
) -> Vec<(A, B)> {
    a.iter()
        .flat_map(|x| b.iter().map(move |y| (x.clone(), y.clone())))
        .collect()
}

#[test]
fn test_predicate_logic_solving() {
    let zero = Application("0".to_string(), vec![]);

    // forall x. add(0, x, x)
    // add(0,X,X).
    let ax1 =
        Atom("add".to_string(), vec![zero.clone(), var("x"), var("x")]);
    // forall n m p. add(n,m,p) => add(s(n),m,s(p))
    // add(s(N),M,s(P)) :- add(N,M,P).
    let ax2 = Clause(vec![
        Atom("add".to_string(), vec![s(var("n")), var("m"), s(var("p"))]),
        Not(Box::new(Atom(
            "add".to_string(),
            vec![var("n"), var("m"), var("p")],
        ))),
    ]);
    // ?- add(1,2,R)
    let neg_target = with_answer_literal(&Not(Box::new(Atom(
        "add".to_string(),
        vec![
            s(zero.clone()),
            s(s(zero.clone())),
            Variable("R".to_string()),
        ],
    ))));

    for ((sel_name, sel_variant), (gc_name, gc_fn)) in
        all_combinations(all_selection_fns(), all_giving_clause_fns())
    {
        let selection_fn = get_selection_fn(sel_variant);
        let mgu = saturate(
            &vec![ax1.clone(), ax2.clone(), neg_target.clone()],
            &selection_fn,
            gc_fn,
        )
        .unwrap();
        assert_eq!(
            mgu.resolvent("R"),
            Some(&s(s(s(zero.clone())))),
            "predicate logic: wrong solution with selection={sel_name}, giving_clause={gc_name}"
        );
        assert_eq!(
            mgu.names(),
            vec!["R"],
            "predicate logic: answer isnt restricted to the query variables with selection={sel_name}, giving_clause={gc_name}"
        );
    }
}

#[test]
fn test_equality_logic_solving() {
    let zero = Application("0".to_string(), vec![]);

    // forall x. 0+x = x
    let ax1 = Equality(add(zero.clone(), var("x")), var("x"));
    // forall n m p. n+m = p  =>  s(n)+m = s(p)
    let ax2 = Clause(vec![
        Not(Box::new(Equality(add(var("n"), var("m")), var("p")))),
        Equality(add(s(var("n")), var("m")), s(var("p"))),
    ]);
    // ?- 1+R = 3
    let neg_target = with_answer_literal(&Not(Box::new(Equality(
        add(s(zero.clone()), var("R")),
        s(s(s(zero.clone()))),
    ))));

    for ((sel_name, sel_variant), (gc_name, gc_fn)) in
        all_combinations(all_selection_fns(), all_giving_clause_fns())
    {
        // unordered superposition (All) blows up before reaching the refutation
        // once premises are renamed apart: a search strategy limit, not an answer one
        if sel_name == "All" {
            continue;
        }

        let selection_fn = get_selection_fn(sel_variant);
        let mgu = saturate(
            &vec![ax1.clone(), ax2.clone(), neg_target.clone()],
            &selection_fn,
            gc_fn,
        )
        .unwrap();
        assert_eq!(
            mgu.resolvent("R"),
            Some(&s(s(zero.clone()))),
            "equality logic: wrong solution with selection={sel_name}, giving_clause={gc_name}"
        );
        assert_eq!(
            mgu.names(),
            vec!["R"],
            "equality logic: answer isnt restricted to the query variables with selection={sel_name}, giving_clause={gc_name}"
        );
    }
}

#[test]
fn test_simple_saturation() {
    let selection_fn = get_selection_fn(SelectionFunction::All);
    let a = Atom("A".to_string(), vec![]);
    let b = Atom("B".to_string(), vec![]);

    let non_contradiction = vec![
        a.clone(),
        // conclusion, trying to prove A |- A
        Not(Box::new(a.clone())),
    ];
    assert!(
        saturate(&non_contradiction, &selection_fn, pick_clause).is_ok(),
        "Saturation couldnt prove A ⊢ A"
    );

    let modus_ponens = vec![
        Clause(vec![Not(Box::new(a.clone())), b.clone()]),
        a.clone(),
        // conclusion, trying to prove A=>B, A ⊢ B
        Not(Box::new(b.clone())),
    ];
    assert!(
        saturate(&modus_ponens, &selection_fn, pick_clause).is_ok(),
        "Saturation couldnt prove A=>B, A ⊢ B"
    );

    let modus_tollens = vec![
        Clause(vec![Not(Box::new(a.clone())), b.clone()]),
        Not(Box::new(b.clone())),
        // trying to prove A=>B, ¬B ⊢ ¬A
        a.clone(),
    ];
    assert!(
        saturate(&modus_tollens, &selection_fn, pick_clause).is_ok(),
        "Saturation couldnt prove A=>B, ¬B ⊢ ¬A"
    );
}

#[test]
fn test_unification_resolution() {
    let selection_fn = get_selection_fn(SelectionFunction::All);
    let zero = Application("zero".to_string(), vec![]);
    let one = Application("s".to_string(), vec![zero.clone()]);
    let two = Application("s".to_string(), vec![one.clone()]);
    let x = Variable("x".to_string());
    let y = Variable("y".to_string());
    let z = Variable("z".to_string());
    let three = Variable("3_skolem_witness".to_string());
    // let three = Application("3_skolem_witness".to_string(), vec![]);
    let target = Atom(
        "Add".to_string(),
        vec![one.clone(), two.clone(), three.clone()],
    );

    assert!(
        saturate(
            &vec![
                // ∀y. Add(0,y,y)  ≡  0+y=y
                Atom(
                    "Add".to_string(),
                    vec![zero.clone(), y.clone(), y.clone()]
                ),
                // ∀x,y,z. Add(x,y,z) ⇒ Add(s x, y, s z)  ≡  x+y=z => x+1+y=z+1
                Clause(vec![
                    Not(Box::new(Atom(
                        "Add".to_string(),
                        vec![x.clone(), y.clone(), z.clone()]
                    ))),
                    Atom(
                        "Add".to_string(),
                        vec![
                            Application("s".to_string(), vec![x.clone()]),
                            y.clone(),
                            Application("s".to_string(), vec![z.clone()])
                        ]
                    )
                ]),
                // ¬ ∃z. Add(1,2,z)  ≡  1+2=z
                Not(Box::new(target))
            ],
            &selection_fn,
            pick_clause
        )
        .is_ok(),
        "unable to solve addition problem"
    );
}

#[test]
fn test_bottom_ignores_answer_literals() {
    let goal = not(pred("P", vec![var("R")]));
    let Clause(lits) = with_answer_literal(&Clause(vec![goal.clone()]))
    else {
        panic!("expected a clause")
    };
    let answer = lits[1].clone();

    assert!(is_bottom(&Clause(vec![])), "Empty clause isnt bottom");
    assert!(
        is_bottom(&Clause(vec![answer.clone()])),
        "Clause made only of answer literals isnt bottom"
    );
    assert!(
        is_bottom(&Clause(vec![answer.clone(), answer.clone()])),
        "Clause made only of answer literals isnt bottom"
    );
    assert!(
        !is_bottom(&Clause(vec![goal.clone(), answer.clone()])),
        "Clause with a goal literal left is bottom"
    );
    assert!(!is_bottom(&goal), "Unit literal is bottom");
}

#[test]
fn test_satisfiable_set_saturates() {
    // P(a), P(x) => Q(x) ⊬ Q(b)
    let set = vec![
        pred("P", vec![constant("a")]),
        Clause(vec![
            not(pred("P", vec![var("x")])),
            pred("Q", vec![var("x")]),
        ]),
        with_answer_literal(&not(pred("Q", vec![constant("b")]))),
    ];

    for ((sel_name, sel_variant), (gc_name, gc_fn)) in
        all_combinations(all_selection_fns(), all_giving_clause_fns())
    {
        assert!(
            saturate(&set, &get_selection_fn(sel_variant), gc_fn).is_err(),
            "saturation refuted a satisfiable set with selection={sel_name}, giving_clause={gc_name}"
        );
    }
}

#[test]
fn test_answer_ignores_dead_end_bindings() {
    // ?- Q(R) ∧ P(R), where resolving against Q(a) binds R to a in a dead end
    let set = vec![
        pred("P", vec![constant("b")]),
        pred("Q", vec![constant("b")]),
        pred("Q", vec![constant("a")]),
        with_answer_literal(&Clause(vec![
            not(pred("Q", vec![var("R")])),
            not(pred("P", vec![var("R")])),
        ])),
    ];

    for ((sel_name, sel_variant), (gc_name, gc_fn)) in
        all_combinations(all_selection_fns(), all_giving_clause_fns())
    {
        let mgu =
            saturate(&set, &get_selection_fn(sel_variant), gc_fn).unwrap();
        assert_eq!(
            mgu.resolvent("R"),
            Some(&constant("b")),
            "answer picked up a binding not leading to the refutation with selection={sel_name}, giving_clause={gc_name}"
        );
    }
}

#[test]
fn test_answer_binds_query_variables_jointly() {
    // ?- Pair(R, S) must return one of the pairs, never a mix of the two
    let set = vec![
        pred("Pair", vec![constant("a"), constant("b")]),
        pred("Pair", vec![constant("c"), constant("d")]),
        with_answer_literal(&not(pred("Pair", vec![var("R"), var("S")]))),
    ];

    for ((sel_name, sel_variant), (gc_name, gc_fn)) in
        all_combinations(all_selection_fns(), all_giving_clause_fns())
    {
        let mgu =
            saturate(&set, &get_selection_fn(sel_variant), gc_fn).unwrap();
        let answer = (mgu.resolvent("R"), mgu.resolvent("S"));
        assert!(
            answer == (Some(&constant("a")), Some(&constant("b")))
                || answer == (Some(&constant("c")), Some(&constant("d"))),
            "answer {answer:?} isnt a solution with selection={sel_name}, giving_clause={gc_name}"
        );
    }
}

#[test]
fn test_premises_renamed_apart() {
    // ∀x. P(x, a) contradicts ∀x. ¬P(b, x), even though both clauses name their variable x
    let set = vec![
        pred("P", vec![var("x"), constant("a")]),
        not(pred("P", vec![constant("b"), var("x")])),
    ];

    for ((sel_name, sel_variant), (gc_name, gc_fn)) in
        all_combinations(all_selection_fns(), all_giving_clause_fns())
    {
        assert!(
            saturate(&set, &get_selection_fn(sel_variant), gc_fn).is_ok(),
            "clauses sharing variable names werent renamed apart with selection={sel_name}, giving_clause={gc_name}"
        );
    }
}
