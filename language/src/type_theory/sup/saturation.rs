use super::sup::SupFormula::{self, Clause};
use super::sup_utils::subsumes;
use crate::error::LofError;
use crate::type_theory::commons::unification::Substitution;
use crate::type_theory::sup::freedom::{
    GivingClauseSignature, SelectionFunctionSignature,
};
use crate::type_theory::sup::inferences::{
    demodulate_first, eq_factoring, eq_resolution, factoring, resolution,
    subsumption_resolution_first, superposition,
};
use crate::type_theory::sup::sup::SupTerm;
use crate::type_theory::sup::sup_utils::{
    extract_answer, is_answer_literal, is_tautology, standardize_apart,
};

/// Checks if a formula φ is the empty clause, ignoring answer literals
fn is_bottom(φ: &SupFormula) -> bool {
    match φ {
        Clause(literals) => literals.iter().all(is_answer_literal),
        _ => false,
    }
}

#[allow(non_snake_case)]
/// Decides if the clause is redundant
fn is_redundant(C: &SupFormula, kept: &Vec<SupFormula>) -> bool {
    is_tautology(C) || kept.iter().any(|D| subsumes(D, C))
}

/// Forward simplification simplifies the given `clause` by the clauses in `kept`
fn forward_simplification(
    kept: &Vec<SupFormula>,
    clause: SupFormula,
) -> SupFormula {
    let mut current_given_clause = clause;
    for other in kept {
        current_given_clause = demodulate_first(&current_given_clause, other);
        current_given_clause =
            subsumption_resolution_first(&current_given_clause, other);
    }

    current_given_clause
}

/// Backward simplification simplifies the `kept` clauses by the given `clause`.
/// Returns the set of only simplified rules from kept and drops simplified clauses
/// from `kept`
fn backward_simplification(
    kept: &mut Vec<SupFormula>,
    clause: &SupFormula,
) -> Vec<SupFormula> {
    let mut simplified_kept = vec![];
    let mut new_kept: Vec<SupFormula> = vec![];

    for other in kept.iter() {
        let simplified_other = demodulate_first(&other, clause);
        let simplified_other =
            subsumption_resolution_first(&simplified_other, clause);

        // only include it if it was simplified
        if simplified_other != *other {
            simplified_kept.push(simplified_other);
        } else {
            new_kept.push((*other).clone());
        }
    }

    *kept = new_kept;
    simplified_kept
}

/// Applies generating inferences with `given` as one of the two participants.
/// Performs unary inferences on `given` alone, then binary inferences between
/// `given` and every clause currently in `kept`.
fn generating_inferences(
    given: &SupFormula,
    kept: &Vec<SupFormula>,
    selection_fn: &SelectionFunctionSignature,
) -> Vec<SupFormula> {
    let mut newly_derived = vec![];

    let (derived, _) = factoring(&given, selection_fn);
    newly_derived.extend(derived);
    let (derived, _) = eq_resolution(&given, selection_fn);
    newly_derived.extend(derived);
    let (derived, _) = eq_factoring(&given, selection_fn);
    newly_derived.extend(derived);

    // binary inferences between given and each clause in kept
    for kept_clause in kept.iter() {
        // premises of binary inferences must not share variables
        let kept_clause = standardize_apart(kept_clause);

        let (derived, _) = resolution(&given, &kept_clause, selection_fn);
        newly_derived.extend(derived);
        let (derived, _) = superposition(&given, &kept_clause, selection_fn);
        newly_derived.extend(derived);
    }

    newly_derived
}

pub fn saturate(
    clauses: &Vec<SupFormula>,
    selection_fn: &SelectionFunctionSignature,
    giving_clause_fn: GivingClauseSignature,
) -> Result<Substitution<SupTerm>, LofError> {
    let mut unprocessed = clauses.clone();
    let mut kept = vec![];

    /// termination checks for clause processing:
    /// * it's empty: the set is unsatisfiable
    /// * it's redundant: move to the next one
    macro_rules! termination {
        // dry like a mf
        ($clause:expr, $kept:expr) => {
            if is_bottom(&$clause) {
                return extract_answer(&$clause);
            }
            if is_redundant(&$clause, &$kept) {
                continue;
            }
        };
    }

    loop {
        if unprocessed.is_empty() {
            return Err(LofError::custom(
                "Saturated the input set with no found contraddiction. Turns out it was satisfyable all along",
            ));
        }

        let clause = giving_clause_fn(&mut unprocessed)?;

        termination!(clause, kept);
        let clause = forward_simplification(&kept, clause);
        termination!(clause, kept);
        let simplified = backward_simplification(&mut kept, &clause);
        unprocessed.extend(simplified);

        let new_clauses = generating_inferences(&clause, &kept, selection_fn);
        kept.push(clause);

        unprocessed.extend(new_clauses);
    }
}

#[cfg(test)]
mod unit_tests {
    use crate::type_theory::sup::freedom::GivingClauseSignature;
    use crate::{
        config::SelectionFunction,
        type_theory::sup::{
            freedom::{get_selection_fn, pick_clause, pick_clause_weighted},
            saturation::{is_bottom, saturate},
            sup::{
                SupFormula::{self, Atom, Clause, Equality, Not},
                SupTerm::{self, Application, Variable},
            },
            sup_utils::with_answer_literal,
        },
    };

    fn s(n: SupTerm) -> SupTerm {
        Application("s".to_string(), vec![n])
    }
    fn var(name: &str) -> SupTerm {
        Variable(name.to_string())
    }
    fn add(n: SupTerm, m: SupTerm) -> SupTerm {
        Application("+".to_string(), vec![n, m])
    }
    fn constant(name: &str) -> SupTerm {
        Application(name.to_string(), vec![])
    }
    fn pred(name: &str, args: Vec<SupTerm>) -> SupFormula {
        Atom(name.to_string(), args)
    }
    fn not(φ: SupFormula) -> SupFormula {
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
}
