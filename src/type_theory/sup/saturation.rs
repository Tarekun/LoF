use super::sup::SupFormula::{self, Clause};
use super::sup_utils::subsumes;
use crate::type_theory::interface::Automatic;
use crate::type_theory::sup::inferences::{
    demodulate_first, subsumption_resolution_first,
};
use crate::type_theory::sup::sup::Sup;
use crate::type_theory::sup::sup_utils::is_tautology;

/// Checks if a formula φ is the empty clause
fn is_bottom(φ: &SupFormula) -> bool {
    match φ {
        Clause(literals) => literals.is_empty(),
        _ => false,
    }
}

/// Selects the next clause to be processed and removes it from the set
fn pick_clause(clauses: &mut Vec<SupFormula>) -> Result<SupFormula, String> {
    if clauses.is_empty() {
        Err("Empty set of clauses received, can't pick any out".to_string())
    } else {
        // TODO here we should generalize this so i can also support stuff like
        // weight/age ratio
        let (max_index, _) = clauses
            .iter()
            .enumerate()
            .max_by(|(_, c1), (_, c2)| Sup::compare_types(c1, c2))
            .unwrap();

        Ok(clauses.remove(max_index))
    }
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

pub fn saturate(clauses: &Vec<SupFormula>) -> Result<(), String> {
    let mut unprocessed = clauses.clone();
    let mut kept = vec![];

    loop {
        while !unprocessed.is_empty() {
            let clause = pick_clause(&mut unprocessed)?;

            termination!(clause, kept);
            let clause = forward_simplification(&kept, clause);
            termination!(clause, kept);
            let simplified = backward_simplification(&mut kept, &clause);

            //these should subsume and drop some clauses in kept next cycle
            unprocessed.extend(simplified);
            kept.push(clause);
        }

        // generating inferences into unprocessed
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
