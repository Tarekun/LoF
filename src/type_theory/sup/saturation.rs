use super::sup::SupFormula::{self, Clause};
use super::sup_utils::subsumes;
use crate::type_theory::sup::inferences::{
    demodulate_first, eq_factoring, eq_resolution, factoring, resolution,
    subsumption_resolution_first, superposition,
};
use crate::type_theory::sup::sup_utils::{
    is_tautology, SelectionFunctionSignature,
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
    ($clause:expr, $kept:expr) => {
        if is_bottom(&$clause) {
            return Ok(());
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
    kept: &Vec<SupFormula>,
    selection_fn: &SelectionFunctionSignature,
) -> Vec<SupFormula> {
    let mut newly_derived = vec![];

    for i in 0..kept.len() {
        println!("\ngenerating inference with {:?}", kept[i]);
        // unary inferences
        if let Ok(derived) = factoring(&kept[i], &selection_fn) {
            println!("applied factoring");
            newly_derived.push(derived);
        }
        if let Ok(derived) = eq_resolution(&kept[i], &selection_fn) {
            println!("applied eq_resolution");
            newly_derived.push(derived);
        }
        if let Ok(derived) = eq_factoring(&kept[i], &selection_fn) {
            println!("applied eq_factoring");
            newly_derived.push(derived);
        }

        // binary inferences
        for j in i + 1..kept.len() {
            println!(
                "binary generating inference with {:?} and {:?}",
                kept[i], kept[j]
            );
            if let Ok(derived) = resolution(&kept[i], &kept[j], &selection_fn) {
                println!("applied resolution");
                newly_derived.push(derived);
            }
            if let Ok(derived) =
                superposition(&kept[i], &kept[j], &selection_fn)
            {
                println!("applied superposition");
                newly_derived.push(derived);
            }
        }
    }

    newly_derived
}

pub fn saturate(
    clauses: &Vec<SupFormula>,
    selection_fn: &SelectionFunctionSignature,
) -> Result<(), String> {
    let mut unprocessed = clauses.clone();
    let mut kept = vec![];

    loop {
        while !unprocessed.is_empty() {
            println!(
                "\nsimplification iteration, unprocessed is {:?}",
                unprocessed
            );
            let clause = pick_clause(&mut unprocessed)?;
            println!("picked clause was {:?}", clause);

            termination!(clause, kept);
            println!("passed termination test");
            let clause = forward_simplification(&kept, clause);
            println!("picked clause after simplification {:?}", clause);
            termination!(clause, kept);
            println!("passed termination test");
            let simplified = backward_simplification(&mut kept, &clause);

            unprocessed.extend(simplified);
            kept.push(clause);
        }

        println!("finished simplification loop with kept {:?}", kept);
        unprocessed = generating_inferences(&kept, &selection_fn);
        println!("newly derived unprocessed {:?}", unprocessed);
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
            saturation::saturate,
            sup::SupFormula::{Atom, Clause, Not},
            sup_utils::get_selection_fn,
        },
    };

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
}

// // Attempt to unify two terms, returning a most-general unifier σ if successful.
// fn unify_terms(t1: &SupTerm, t2: &SupTerm) -> Option<Substitution> {
//     fn solver(t1: &SupTerm, t2: &SupTerm, σ: &mut Substitution) -> bool {
//         let s1 = apply_subst_term(t1, σ);
//         let s2 = apply_subst_term(t2, σ);

//         match (&s1, &s2) {
//             (Variable(x), _) => {
//                 σ.insert(x.clone(), s2.clone());
//                 true
//             }
//             (_, Variable(x)) => {
//                 σ.insert(x.clone(), s1.clone());
//                 true
//             }
//             (Application(f1, args1), Application(f2, args2))
//                 if f1 == f2 && args1.len() == args2.len() =>
//             {
//                 for (a1, a2) in args1.iter().zip(args2.iter()) {
//                     if !solver(a1, a2, σ) {
//                         return false;
//                     }
//                 }
//                 true
//             }
//             _ => false,
//         }
//     }

//     let mut σ = Substitution::new();
//     if solver(t1, t2, &mut σ) {
//         Some(σ)
//     } else {
//         None
//     }
// }

// // Attempt to unify two literals if they are complementary (one positive, one negated).
// // Returns a substitution σ if they unify, else None.
// fn unify_literals(l1: &Literal, l2: &Literal) -> Option<Substitution> {
//     match (l1, l2) {
//         (Literal::Pred(p, args1), Literal::NotPred(q, args2))
//         | (Literal::NotPred(p, args1), Literal::Pred(q, args2)) => {
//             if p == q && args1.len() == args2.len() {
//                 // unify the argument lists
//                 let mut σ = Substitution::new();
//                 for (t1, t2) in args1.iter().zip(args2.iter()) {
//                     if let Some(sub) = unify_terms(
//                         &apply_subst_term(t1, &σ),
//                         &apply_subst_term(t2, &σ),
//                     ) {
//                         // merge sub into σ
//                         for (k, v) in sub {
//                             σ.insert(k, v);
//                         }
//                     } else {
//                         return None;
//                     }
//                 }
//                 return Some(σ);
//             }
//         }
//         (Literal::Eq(s1, t1), Literal::NotEq(s2, t2))
//         | (Literal::NotEq(s1, t1), Literal::Eq(s2, t2)) => {
//             // unify equalities vs. inequalities similarly
//             // (This resolution is analogous to predicates.)
//             let mut σ = Substitution::new();
//             if let Some(sub) = unify_terms(s1, s2) {
//                 for (k, v) in sub {
//                     σ.insert(k, v);
//                 }
//                 if let Some(sub2) = unify_terms(
//                     &apply_subst_term(t1, &σ),
//                     &apply_subst_term(t2, &σ),
//                 ) {
//                     for (k, v) in sub2 {
//                         σ.insert(k, v);
//                     }
//                     return Some(σ);
//                 }
//             }
//         }
//         _ => {}
//     }
//     None
// }
