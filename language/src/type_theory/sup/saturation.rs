use super::sup::SupFormula::{self, Atom, Clause, Equality, ForAll, Not};
use super::sup::SupTerm::{Application, Variable};
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
    is_tautology, standardize_apart, unpack_literals,
};
use std::collections::HashMap;

//########################### ANSWER TRACKING
/// Predicate name prefix of the bookkeeping literals that carry the answer
/// substitution through a derivation (Green's answer-literal method).
///
/// Reassembling the answer by merging every inference's mgu into one flat
/// map can't work: clauses are renamed apart as they're derived (they have
/// to be, see `generating_inferences`), so a binding recorded for `m` in one
/// step has nothing to do with the `m` of another step, and the two only
/// ever chained up by accident. An answer literal instead *rides along* in
/// the clause, so every substitution the calculus applies to that clause is
/// applied to the recorded answer too, renaming included.
const ANSWER_PREFIX: &str = "$answer_";

fn is_answer_literal(φ: &SupFormula) -> bool {
    matches!(φ, Atom(name, _) if name.starts_with(ANSWER_PREFIX))
}

/// Splits a clause's literals into its ordinary ones and its answer literals
fn split_answer_literals(
    φ: &SupFormula
) -> (Vec<SupFormula>, Vec<SupFormula>) {
    unpack_literals(φ)
        .into_iter()
        .partition(|l| !is_answer_literal(l))
}

/// Drops a clause's answer literals, leaving the logical content the
/// calculus's redundancy checks should be looking at. Clauses without any
/// are returned untouched, so problems that track no variables behave
/// exactly as they would with no answer literals in the picture at all.
fn strip_answer_literals(φ: &SupFormula) -> SupFormula {
    let (body, answers) = split_answer_literals(φ);
    if answers.is_empty() {
        φ.to_owned()
    } else {
        Clause(body)
    }
}

/// Distinct variable names of a formula, in order of first occurrence
fn clause_variables(φ: &SupFormula) -> Vec<String> {
    fn of_term(term: &SupTerm, found: &mut Vec<String>) {
        match term {
            Variable(name) => {
                if !found.contains(name) {
                    found.push(name.to_string());
                }
            }
            Application(_, args) => {
                args.iter().for_each(|arg| of_term(arg, found))
            }
        }
    }
    fn of_formula(φ: &SupFormula, found: &mut Vec<String>) {
        match φ {
            Atom(_, args) => args.iter().for_each(|arg| of_term(arg, found)),
            Equality(left, right) => {
                of_term(left, found);
                of_term(right, found);
            }
            Not(ψ) => of_formula(ψ, found),
            Clause(literals) => {
                literals.iter().for_each(|l| of_formula(l, found))
            }
            ForAll(_, var_type, body) => {
                of_formula(var_type, found);
                of_formula(body, found);
            }
        }
    }

    let mut found = vec![];
    of_formula(φ, &mut found);
    found
}

/// Appends to `φ` an answer literal recording φ's own variables, returning
/// it along with the original variable names those arguments started as.
/// Variable-free clauses get no answer literal: there'd be nothing to solve.
fn with_answer_literal(
    φ: &SupFormula,
    index: usize,
) -> (SupFormula, Vec<String>) {
    let variables = clause_variables(φ);
    if variables.is_empty() {
        return (φ.to_owned(), variables);
    }

    let mut literals = unpack_literals(φ);
    literals.push(Atom(
        format!("{}{}", ANSWER_PREFIX, index),
        variables
            .iter()
            .map(|name| Variable(name.to_string()))
            .collect(),
    ));
    (Clause(literals), variables)
}

/// Reads the answer substitution off a refutation, mapping each original
/// variable name to whatever its answer literal ended up carrying.
///
/// A variable that took *different* values at different points of the same
/// refutation (the recursive rule's own variables do, once it's applied more
/// than once) has no single answer, so it's reported as unsolved rather than
/// as an arbitrary one of its instances.
fn extract_answer(
    φ: &SupFormula,
    origins: &Vec<Vec<String>>,
) -> Substitution<SupTerm> {
    let mut solved: HashMap<String, Option<SupTerm>> = HashMap::new();

    for literal in unpack_literals(φ) {
        let Atom(predicate, args) = &literal else {
            continue;
        };
        let Some(index) = predicate
            .strip_prefix(ANSWER_PREFIX)
            .and_then(|index| index.parse::<usize>().ok())
        else {
            continue;
        };
        let Some(names) = origins.get(index) else {
            continue;
        };

        for (name, value) in names.iter().zip(args.iter()) {
            match solved.get(name) {
                Some(Some(previous)) if previous != value => {
                    solved.insert(name.to_string(), None);
                }
                Some(_) => {}
                None => {
                    solved.insert(name.to_string(), Some(value.to_owned()));
                }
            }
        }
    }

    Substitution::from(
        solved
            .into_iter()
            .filter_map(|(name, value)| Some((name, value?))),
    )
}
//########################### ANSWER TRACKING

/// Checks if a formula φ refutes the input set, ie if it's the empty clause.
/// Answer literals don't count as content: they carry no logical claim, they
/// only record what the refutation bound the original variables to.
fn is_bottom(φ: &SupFormula) -> bool {
    unpack_literals(φ).iter().all(is_answer_literal)
}

#[allow(non_snake_case)]
/// Decides if the clause is redundant
fn is_redundant(C: &SupFormula, kept: &Vec<SupFormula>) -> bool {
    // answer literals are bookkeeping, so they're excluded from redundancy:
    // otherwise every clause would carry differently instantiated ones and
    // subsumption would essentially never fire again
    let C = strip_answer_literals(C);
    is_tautology(&C)
        || kept.iter().any(|D| subsumes(&strip_answer_literals(D), &C))
}

/// Simplifies `clause` by `other` (demodulation + subsumption resolution),
/// keeping `clause`'s answer literals attached: `subsumption_resolution_first`
/// is free to drop a leading literal, which for an answer literal would
/// silently throw away part of the answer. Demodulation still reaches them,
/// so equalities keep rewriting the recorded answer as the proof proceeds.
fn simplify_by(clause: SupFormula, other: &SupFormula) -> SupFormula {
    let (body, answers) = split_answer_literals(&clause);
    if answers.is_empty() {
        let simplified = demodulate_first(&clause, other);
        return subsumption_resolution_first(&simplified, other);
    }

    let simplified = demodulate_first(&Clause(body.clone()), other);
    let simplified = subsumption_resolution_first(&simplified, other);
    let simplified_body = unpack_literals(&simplified);
    let simplified_answers: Vec<SupFormula> =
        answers.iter().map(|a| demodulate_first(a, other)).collect();

    // returning `clause` itself when nothing changed keeps this a no-op for
    // the caller, which compares against the original to detect simplification
    if simplified_body == body && simplified_answers == answers {
        return clause;
    }

    let mut literals = simplified_body;
    literals.extend(simplified_answers);
    Clause(literals)
}

/// Forward simplification simplifies the given `clause` by the clauses in `kept`
fn forward_simplification(
    kept: &Vec<SupFormula>,
    clause: SupFormula,
) -> SupFormula {
    kept.iter().fold(clause, simplify_by)
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
        let simplified_other = simplify_by((*other).clone(), clause);

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

    // Answer literals are bookkeeping and must never be *selected*: they
    // can't be resolved against anything (nothing ever negates them), so a
    // clause whose answer literal came out maximal would have no selected
    // literal left to work with and would go inert - which is easy to hit,
    // since a clause with more variables than its predicate has arguments
    // gets an answer literal that outweighs its real ones. Hiding them from
    // the configured selection function keeps them out of the running while
    // still leaving them in the clause, so inferences carry them along and
    // apply their substitutions to them.
    let selection_fn = |literals: &mut Vec<SupFormula>| {
        let (mut body, answers) =
            split_answer_literals(&Clause(literals.to_vec()));
        let selected = selection_fn(&mut body);
        *literals = body;
        literals.extend(answers);
        selected
    };

    // the mgus these return are dropped on purpose: the answer substitution
    // is carried by each clause's own answer literals (see ANSWER_PREFIX),
    // which is the only representation that survives the renaming below
    newly_derived.extend(factoring(&given, &selection_fn).0);
    newly_derived.extend(eq_resolution(&given, &selection_fn).0);
    newly_derived.extend(eq_factoring(&given, &selection_fn).0);

    // binary inferences between given and each clause in kept
    for kept_clause in kept.iter() {
        newly_derived.extend(resolution(&given, &kept_clause, &selection_fn).0);
        newly_derived
            .extend(superposition(&given, &kept_clause, &selection_fn).0);
    }

    // Rename every derived clause apart. `kept` clauses are reused against
    // each new given clause, so without this a variable surviving from one
    // use of a clause collides with the same-named variable of a later use,
    // and the unifier - which compares variables by name - silently builds a
    // circular substitution instead of failing. That corrupts the derived
    // clause and makes proofs unreachable: `test_deep_recursion_needs_renaming`
    // below pins down the smallest problem where dropping this loses a proof.
    // newly_derived
    newly_derived.iter().map(standardize_apart).collect()
}

pub fn saturate(
    clauses: &Vec<SupFormula>,
    selection_fn: &SelectionFunctionSignature,
    giving_clause_fn: GivingClauseSignature,
) -> Result<Substitution<SupTerm>, LofError> {
    // every input clause gets an answer literal recording its own variables
    // and is then renamed apart, so no two of them can share a name either
    let mut origins = vec![];
    let mut unprocessed = vec![];
    for (index, clause) in clauses.iter().enumerate() {
        let (augmented, variables) = with_answer_literal(clause, index);
        origins.push(variables);
        unprocessed.push(standardize_apart(&augmented));
    }
    let mut kept = vec![];

    /// termination checks for clause processing:
    /// * it's empty: the set is unsatisfiable
    /// * it's redundant: move to the next one
    macro_rules! termination {
        // dry like a mf
        ($clause:expr, $kept:expr) => {
            if is_bottom(&$clause) {
                return Ok(extract_answer(&$clause, &origins));
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
    use crate::error::LofError;
    use crate::type_theory::commons::unification::Substitution;
    use crate::type_theory::sup::freedom::{
        GivingClauseSignature, SelectionFunctionSignature,
    };
    use crate::{
        config::SelectionFunction,
        type_theory::sup::{
            freedom::{get_selection_fn, pick_clause, pick_clause_weighted},
            saturation::saturate,
            sup::{
                SupFormula::{self, Atom, Clause, Equality, Not},
                SupTerm::{self, Application, Variable},
            },
        },
    };
    use std::sync::mpsc;
    use std::time::Duration;

    /// Runs `saturate` on a background thread bounded by `timeout`,
    /// collapsing a timeout into an `Err` so callers can treat it exactly
    /// like a normal `saturate` result. Self-contained here rather than a
    /// change to `saturate` itself: some axiom sets (eg a recursive
    /// successor rule) have an infinite family of non-redundant
    /// consequences, so "no contradiction found" can only ever be
    /// confirmed by running forever, never by a definite `Err` return -
    /// treating "didn't finish in time" the same as "didn't find a proof"
    /// is the honest way to keep a test like that from hanging forever.
    fn saturate_bounded(
        clauses: Vec<SupFormula>,
        selection_fn: SelectionFunctionSignature,
        giving_clause_fn: GivingClauseSignature,
        timeout: Duration,
    ) -> Result<Substitution<SupTerm>, LofError> {
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            let _ =
                tx.send(saturate(&clauses, &selection_fn, giving_clause_fn));
        });
        rx.recv_timeout(timeout).unwrap_or_else(|_| {
            Err(LofError::custom(
                "saturation didn't terminate within the test's time budget",
            ))
        })
    }

    fn s(n: SupTerm) -> SupTerm {
        Application("s".to_string(), vec![n])
    }
    fn var(name: &str) -> SupTerm {
        Variable(name.to_string())
    }
    fn add(n: SupTerm, m: SupTerm) -> SupTerm {
        Application("+".to_string(), vec![n, m])
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

    /// Pins down why `generating_inferences` renames every derived clause
    /// apart. `add(3,1,R)` is the smallest problem where dropping that
    /// renaming loses the proof: it needs the recursive rule three times, and
    /// by the third use a variable surviving from the first use collides with
    /// the rule's own same-named variable. The unifier compares variables by
    /// name, so it can't tell them apart and quietly builds a circular
    /// substitution (`p -> m`, `m -> s(p)`) that the occurs check misses -
    /// it only looks at the term being inserted, not through existing
    /// aliases - producing a corrupted clause the refutation can't use.
    ///
    /// Two applications of the rule (`add(2,*,R)`) still succeed without the
    /// renaming, which is why the pre-existing tests never caught this.
    /// Every selection/giving-clause combination fails without it and
    /// succeeds with it, so this doesn't depend on a particular strategy.
    #[test]
    fn test_deep_recursion_needs_renaming_apart() {
        let zero = Application("0".to_string(), vec![]);
        let number = |n: usize| (0..n).fold(zero.clone(), |acc, _| s(acc));

        // add(0,X,X).
        let ax1 =
            Atom("add".to_string(), vec![zero.clone(), var("x"), var("x")]);
        // add(s(N),M,s(P)) :- add(N,M,P).
        let ax2 = Clause(vec![
            Atom("add".to_string(), vec![s(var("n")), var("m"), s(var("p"))]),
            Not(Box::new(Atom(
                "add".to_string(),
                vec![var("n"), var("m"), var("p")],
            ))),
        ]);
        // ?- add(3,1,R)
        let neg_target = Not(Box::new(Atom(
            "add".to_string(),
            vec![number(3), number(1), var("R")],
        )));

        for ((sel_name, sel_variant), (gc_name, gc_fn)) in
            all_combinations(all_selection_fns(), all_giving_clause_fns())
        {
            let selection_fn = get_selection_fn(sel_variant);
            let mgu = saturate(
                &vec![ax1.clone(), ax2.clone(), neg_target.clone()],
                &selection_fn,
                gc_fn,
            );
            assert_eq!(
                mgu.as_ref().map(|mgu| mgu.resolvent("R")),
                Ok(Some(&number(4))),
                "three levels of recursion need derived clauses renamed apart, but selection={sel_name}, giving_clause={gc_name} got {mgu:?}"
            );
        }
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
        let neg_target = Not(Box::new(Atom(
            "add".to_string(),
            vec![
                s(zero.clone()),
                s(s(zero.clone())),
                Variable("R".to_string()),
            ],
        )));
        // unsolvable equation 1+2 = 4
        let inconsistent = Not(Box::new(Atom(
            "add".to_string(),
            vec![
                s(zero.clone()),
                s(s(zero.clone())),
                s(s(s(s(zero.clone())))),
            ],
        )));

        for ((sel_name, sel_variant), (gc_name, gc_fn)) in
            all_combinations(all_selection_fns(), all_giving_clause_fns())
        {
            let selection_fn = get_selection_fn(sel_variant);
            let mgu = saturate(
                &vec![ax1.clone(), ax2.clone(), neg_target.clone()],
                &selection_fn,
                gc_fn,
            );
            assert_eq!(
                mgu.unwrap().resolvent("R"),
                Some(&s(s(s(zero.clone())))),
                "predicate logic: wrong solution with selection={sel_name}, giving_clause={gc_name}"
            );

            // validate its not just passing on anything
            let res = saturate_bounded(
                vec![ax1.clone(), ax2.clone(), inconsistent.clone()],
                selection_fn,
                gc_fn,
                Duration::from_secs(2),
            );
            assert!(
                res.is_err(),
                "saturation is succeeding with incosistent input formulas with selection={sel_name}, giving_clause={gc_name}"
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
        let neg_target = Not(Box::new(Equality(
            add(s(zero.clone()), var("R")),
            s(s(s(zero.clone()))),
        )));

        for ((sel_name, sel_variant), (gc_name, gc_fn)) in
            all_combinations(all_selection_fns(), all_giving_clause_fns())
        {
            // this config keeps generating new non-redundant consequences
            // faster than the refutation is reached
            if sel_name == "All" && gc_name == "FIFO" {
                continue;
            }

            let selection_fn = get_selection_fn(sel_variant);
            let mgu = saturate(
                &vec![ax1.clone(), ax2.clone(), neg_target.clone()],
                &selection_fn,
                gc_fn,
            );
            assert_eq!(
                mgu.unwrap().resolvent("R"),
                Some(&s(s(zero.clone()))),
                "equality logic: wrong solution with selection={sel_name}, giving_clause={gc_name}"
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
}
