use super::sup::SupFormula::{self, Clause};
use super::sup::SupTerm::Variable;
use super::sup_utils::subsumes;
use crate::type_theory::commons::unification::Substitution;
use crate::type_theory::sup::freedom::SelectionFunctionSignature;
use crate::type_theory::sup::inferences::{
    demodulate_first, eq_factoring, eq_resolution, factoring, resolution,
    subsumption_resolution_first, superposition,
};
use crate::type_theory::sup::sup::SupTerm;
use crate::type_theory::sup::sup_utils::{
    is_tautology, substitute_term, type_refresh_variables,
};

/// Checks if a formula φ is the empty clause
fn is_bottom(φ: &SupFormula) -> bool {
    match φ {
        Clause(literals) => literals.is_empty(),
        _ => false,
    }
}

/// Selects the next clause to be processed and removes it from the set
fn pick_clause(clauses: &mut Vec<SupFormula>) -> Result<SupFormula, String> {
    // TODO here we should generalize this so i can also support stuff like weight/age ratio
    Ok(clauses.remove(0))
}

#[allow(non_snake_case)]
/// Decides if the clause is redundant
fn is_redundant(C: &SupFormula, kept: &Vec<SupFormula>) -> bool {
    is_tautology(C) || kept.iter().any(|D| subsumes(D, C))
}

/// termination checks for clause processing:
/// * it's empty: the set is unsatisfiable
/// * it's redundant: move to the next one
macro_rules! termination {
    // dry like a mf
    ($clause:expr, $kept:expr, $mgu:expr) => {
        if is_bottom(&$clause) {
            return Ok($mgu.reduce(|term, var_name, arg| {
                substitute_term(term, &Variable(var_name.to_string()), arg)
            }));
        }
        if is_redundant(&$clause, &$kept) {
            continue;
        }
    };
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

/// Applies superposition inferences to all currently kept formulas.
/// Cost is quadratic in the size of working set of formulas, as for binary
/// inference rules it compares every formula with every other formula once
fn generating_inferences(
    kept: &mut Vec<SupFormula>,
    selection_fn: &SelectionFunctionSignature,
) -> (Vec<SupFormula>, Substitution<SupTerm>) {
    let mut newly_derived = vec![];
    let mut solving_mgu = Substitution::empty();

    for i in 0..kept.len() {
        let (left, right) = kept.split_at_mut(i + 1);
        let mut first_clause: &mut SupFormula = &mut left[i];

        // unary inferences
        let (derived, mgu) = factoring(first_clause, &selection_fn);
        newly_derived.extend(derived);
        solving_mgu.merge(mgu);

        let (derived, mgu) = eq_resolution(first_clause, &selection_fn);
        newly_derived.extend(derived);
        *first_clause = type_refresh_variables(first_clause);
        solving_mgu.merge(mgu);

        let (derived, mgu) = eq_factoring(first_clause, &selection_fn);
        newly_derived.extend(derived);
        solving_mgu.merge(mgu);

        // binary inferences
        for mut second_clause in right.iter_mut() {
            let (derived, mgu) = resolution(
                &mut first_clause,
                &mut second_clause,
                &selection_fn,
            );
            newly_derived.extend(derived);
            solving_mgu.merge(mgu);

            let (derived, mgu) = superposition(
                &mut first_clause,
                &mut second_clause,
                &selection_fn,
            );
            for c in derived {
                newly_derived.push(type_refresh_variables(&c));
            }
            solving_mgu.merge(mgu);
        }
    }

    (newly_derived, solving_mgu)
}

pub fn saturate(
    clauses: &Vec<SupFormula>,
    selection_fn: &SelectionFunctionSignature,
) -> Result<Substitution<SupTerm>, String> {
    let mut unprocessed = clauses.clone();
    let mut kept = vec![];
    let mut solving_mgu = Substitution::empty();

    loop {
        while !unprocessed.is_empty() {
            let clause = pick_clause(&mut unprocessed)?;

            termination!(clause, kept, solving_mgu);
            let clause = forward_simplification(&kept, clause);
            termination!(clause, kept, solving_mgu);
            let simplified = backward_simplification(&mut kept, &clause);

            unprocessed.extend(simplified);
            kept.push(clause);
        }

        let (new_unprocessed, mgu) =
            generating_inferences(&mut kept, &selection_fn);
        unprocessed = new_unprocessed;
        solving_mgu.merge(mgu);
        if unprocessed.len() == 0 {
            return Err(
                "Saturated the input set with no found contraddiction. Turns out it was satisfyable all along".to_string()
            );
        }
    }
}

#[cfg(test)]
mod unit_tests {
    use crate::{
        config::SelectionFunction,
        type_theory::sup::{
            freedom::get_selection_fn,
            saturation::saturate,
            sup::SupFormula::{Atom, Clause, Equality, Not},
            sup::SupTerm::{self, Application, Variable},
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

    #[test]
    fn test_predicate_logic_solving() {
        let zero = Application("0".to_string(), vec![]);
        let selection_fn = get_selection_fn(SelectionFunction::All());

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

        let mgu = saturate(&vec![ax1, ax2, neg_target], &selection_fn);
        assert_eq!(
            mgu.clone().unwrap().resolvent("R"),
            Some(&s(s(s(zero.clone())))),
            "Variable solution of the addition problem is not the expected"
        );
    }

    // #[test]
    // fn test_equality_logic_solving() {
    //     let zero = Application("0".to_string(), vec![]);
    //     let selection_fn = get_selection_fn(SelectionFunction::All());

    //     // forall x. 0+x = x
    //     let ax1 = Equality(add(zero.clone(), var("x")), var("x"));
    //     // forall n m p. n+m = p  =>  s(n)+m = s(p)
    //     let ax2 = Clause(vec![
    //         Not(Box::new(Equality(add(var("n"), var("m")), var("p")))),
    //         Equality(add(s(var("n")), var("m")), s(var("p"))),
    //     ]);
    //     let neg_target = Not(Box::new(Equality(
    //         add(s(zero.clone()), var("R")),
    //         s(s(s(zero.clone()))),
    //     )));

    //     // assert_eq!(
    //     //     superposition(&neg_target, &ax2, &selection_fn),
    //     //     Err("".to_string()),
    //     //     "problema"
    //     // );

    //     let mgu = saturate(&vec![ax1, ax2, neg_target], &selection_fn);
    //     println!("{:?}", mgu.clone().unwrap());
    //     assert_eq!(
    //         mgu.unwrap().resolvent("R"),
    //         // either this or an equivalent expression has to pass
    //         Some(&s(s(zero.clone()))),
    //         "Variable solution of the addition problem is not the expected"
    //     );
    //     panic!();
    // }

    #[test]
    fn test_simple_saturation() {
        let selection_fn = get_selection_fn(SelectionFunction::All());
        let a = Atom("A".to_string(), vec![]);
        let b = Atom("B".to_string(), vec![]);

        let non_contradiction = vec![
            a.clone(),
            // conclusion, trying to prove A |- A
            Not(Box::new(a.clone())),
        ];
        assert!(
            saturate(&non_contradiction, &selection_fn).is_ok(),
            "Saturation couldnt prove A ⊢ A"
        );

        let modus_ponens = vec![
            Clause(vec![Not(Box::new(a.clone())), b.clone()]),
            a.clone(),
            // conclusion, trying to prove A=>B, A ⊢ B
            Not(Box::new(b.clone())),
        ];
        assert!(
            saturate(&modus_ponens, &selection_fn).is_ok(),
            "Saturation couldnt prove A=>B, A ⊢ B"
        );

        let modus_tollens = vec![
            Clause(vec![Not(Box::new(a.clone())), b.clone()]),
            Not(Box::new(b.clone())),
            // trying to prove A=>B, ¬B ⊢ ¬A
            a.clone(),
        ];
        assert!(
            saturate(&modus_tollens, &selection_fn).is_ok(),
            "Saturation couldnt prove A=>B, ¬B ⊢ ¬A"
        );
    }

    #[test]
    fn test_unification_resolution() {
        let selection_fn = get_selection_fn(SelectionFunction::All());
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
                &selection_fn
            )
            .is_ok(),
            "unable to solve addition problem"
        );
    }
}
