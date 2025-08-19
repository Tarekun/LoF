use super::sup::SupFormula::{self, Clause};
use super::sup_utils::subsumes;
use crate::type_theory::interface::Automatic;
use crate::type_theory::sup::sup::Sup;
use crate::type_theory::sup::sup_utils::{
    demodulate_first, is_tautology, subsumption_resolution_first,
};

/// Checks if a formula φ is the empty clause
fn is_bottom(φ: &SupFormula) -> bool {
    match φ {
        Clause(literals) => literals.is_empty(),
        _ => false,
    }
}

/// Selects the next clause to be processed
fn pick_clause(clauses: &mut Vec<SupFormula>) -> Result<SupFormula, String> {
    if clauses.is_empty() {
        Err("Empty set of clauses received, can't pick any out".to_string())
    } else {
        Ok(clauses.remove(0))
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
/// Returns the set of only simplified rules from kept
fn backward_simplification(
    kept: &Vec<SupFormula>,
    clause: &SupFormula,
) -> Vec<SupFormula> {
    let mut simplified_kept = vec![];
    for other in kept {
        let simplified_other = demodulate_first(&other, clause);
        let simplified_other =
            subsumption_resolution_first(&simplified_other, clause);

        // only include it if it was simplified
        if simplified_other != *other {
            simplified_kept.push(simplified_other);
        }
    }

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
            let simplified = backward_simplification(&kept, &clause);

            //these should subsume and drop some clauses in kept next cycle
            unprocessed.extend(simplified);
            kept.push(clause);
        }

        // generating inferences into unprocessed
    }
}

// // Apply subst σ to a term, replacing variables.
// fn apply_subst_term(t: &SupTerm, σ: &Substitution) -> SupTerm {
//     match t {
//         Variable(x) => {
//             if let Some(u) = σ.get(x) {
//                 u.clone()
//             } else {
//                 t.to_owned()
//             }
//         }
//         Application(f, args) => Application(
//             f.to_string(),
//             args.iter().map(|ti| apply_subst_term(ti, σ)).collect(),
//         ),
//     }
// }

// // Apply subst σ to a literal.
// fn apply_subst_literal(lit: &Literal, σ: &Substitution) -> Literal {
//     match lit {
//         Literal::Pred(p, args) => Literal::Pred(
//             p.clone(),
//             args.iter().map(|t| apply_subst_term(t, σ)).collect(),
//         ),
//         Literal::NotPred(p, args) => Literal::NotPred(
//             p.clone(),
//             args.iter().map(|t| apply_subst_term(t, σ)).collect(),
//         ),
//         Literal::Eq(t1, t2) => {
//             Literal::Eq(apply_subst_term(t1, σ), apply_subst_term(t2, σ))
//         }
//         Literal::NotEq(t1, t2) => {
//             Literal::NotEq(apply_subst_term(t1, σ), apply_subst_term(t2, σ))
//         }
//     }
// }

// // Apply subst σ to all literals in a clause, producing a new clause.
// fn apply_subst_clause(clause: &Clause, σ: &Substitution) -> Clause {
//     clause
//         .iter()
//         .map(|lit| apply_subst_literal(lit, σ))
//         .collect()
// }

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

// // Binary resolution: derive all resolvents from C1 and C2.
// fn resolve_clauses(C1: &Clause, C2: &Clause) -> Vec<Clause> {
//     let mut results = Vec::new();
//     for i in 0..C1.len() {
//         for j in 0..C2.len() {
//             let L1 = &C1[i];
//             let L2 = &C2[j];
//             if are_complements(L1, L2) {
//                 if let Some(mut σ) = unify_literals(L1, L2) {
//                     // Build the resolvent: (C1 \ {L1}) ∪ (C2 \ {L2}), then apply σ
//                     let mut resolvent = Vec::new();
//                     // add all literals from C1 except L1
//                     for (k, lit) in C1.iter().enumerate() {
//                         if k != i {
//                             resolvent.push(apply_subst_literal(lit, &σ));
//                         }
//                     }
//                     // add all from C2 except L2
//                     for (k, lit) in C2.iter().enumerate() {
//                         if k != j {
//                             resolvent.push(apply_subst_literal(lit, &σ));
//                         }
//                     }
//                     // If both removed one literal, it's fine. If clause repeats, duplicates, etc.
//                     // (We don't handle tautology or duplicate removal in this toy version.)
//                     results.push(resolvent);
//                 }
//             }
//         }
//     }
//     results
// }

// // Paramodulation (superposition): for each positive equation in C1 and each literal in C2.
// fn superpose_clauses(C1: &Clause, C2: &Clause) -> Vec<Clause> {
//     let mut results = Vec::new();
//     // Iterate each equality literal in C1: we only use positive equalities (Eq).
//     for (i, lit) in C1.iter().enumerate() {
//         if let Literal::Eq(l, r) = lit {
//             // For each literal in C2
//             for (j, lit2) in C2.iter().enumerate() {
//                 // We skip if lit2 itself is an equality literal (to avoid double-equality paramod).
//                 // (For simplicity; actual superposition might allow paramodulating into any literal.)
//                 if let Literal::Pred(_, _) | Literal::NotPred(_, _) = lit2 {
//                     // Try to unify l with a subterm of lit2.
//                     // Here we only try the trivial subterm = the whole literal's term structure.
//                     // A full implementation would traverse subterms inside lit2.
//                     // For simplicity, if the predicate has an argument equal to l, unify them.
//                     // (This is a gross simplification!)
//                     // Better: if lit2 has exactly one argument equal to a term u:
//                     let mut args = match lit2 {
//                         Literal::Pred(_, args) => args.clone(),
//                         Literal::NotPred(_, args) => args.clone(),
//                         _ => continue,
//                     };
//                     for k in 0..args.len() {
//                         let u = &args[k];
//                         if let Some(mut σ) = unify_terms(l, u) {
//                             // Paramodulate: replace u by r in lit2 under σ.
//                             args[k] = apply_subst_term(r, &σ);
//                             // Build new clause: (C1 \ {l=r}) ∪ (C2 \ {lit2 with u}) ∪ {modified lit2}
//                             let mut new_clause = Vec::new();
//                             // C1 without the equality
//                             for (i2, lit1) in C1.iter().enumerate() {
//                                 if i2 != i {
//                                     new_clause
//                                         .push(apply_subst_literal(lit1, &σ));
//                                 }
//                             }
//                             // C2 without the original literal lit2
//                             for (j2, lit3) in C2.iter().enumerate() {
//                                 if j2 != j {
//                                     new_clause
//                                         .push(apply_subst_literal(lit3, &σ));
//                                 }
//                             }
//                             // Add the modified literal
//                             let new_lit = match lit2 {
//                                 Literal::Pred(p, _) => {
//                                     Literal::Pred(p.clone(), args.clone())
//                                 }
//                                 Literal::NotPred(p, _) => {
//                                     Literal::NotPred(p.clone(), args.clone())
//                                 }
//                                 _ => continue,
//                             };
//                             new_clause.push(new_lit);
//                             results.push(new_clause);
//                         }
//                     }
//                 }
//             }
//         }
//     }
//     results
// }
