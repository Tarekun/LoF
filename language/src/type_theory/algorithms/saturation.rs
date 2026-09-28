use crate::error::LofError;
use crate::type_theory::commons::unification::Substitution;
use crate::type_theory::grammars::cnf::{
    CnfFormula::{self, Clause},
    CnfTerm,
};
use crate::type_theory::grammars::traits::{Complement, ToCnfFormula};
use crate::type_theory::sup::freedom::{
    GivingClauseSignature, SelectionFunctionSignature,
};
use crate::type_theory::sup::inferences::{
    demodulate_first, eq_factoring, eq_resolution, factoring, resolution,
    subsumption_resolution_first, superposition,
};
use crate::type_theory::sup::sup_utils::{
    extract_answer, is_answer_literal, with_answer_literal,
};

/// Checks if a formula φ is the empty clause, ignoring answer literals
fn is_bottom(φ: &CnfFormula) -> bool {
    match φ {
        Clause(literals) => literals.iter().all(is_answer_literal),
        _ => false,
    }
}

#[allow(non_snake_case)]
/// Decides if the clause is redundant
fn is_redundant(C: &CnfFormula, kept: &Vec<CnfFormula>) -> bool {
    C.is_tautology() || kept.iter().any(|D| D.subsumes(C))
}

/// Forward simplification simplifies the given `clause` by the clauses in `kept`
fn forward_simplification(
    kept: &Vec<CnfFormula>,
    clause: CnfFormula,
) -> CnfFormula {
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
    kept: &mut Vec<CnfFormula>,
    clause: &CnfFormula,
) -> Vec<CnfFormula> {
    let mut simplified_kept = vec![];
    let mut new_kept: Vec<CnfFormula> = vec![];

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
    given: &CnfFormula,
    kept: &Vec<CnfFormula>,
    selection_fn: &SelectionFunctionSignature,
) -> Vec<CnfFormula> {
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
        let kept_clause = kept_clause.standardize_apart();

        let (derived, _) = resolution(&given, &kept_clause, selection_fn);
        newly_derived.extend(derived);
        let (derived, _) = superposition(&given, &kept_clause, selection_fn);
        newly_derived.extend(derived);
    }

    newly_derived
}

/// Saturation loop implementation. Simply computes the derivation colusure
/// of `clauses`, using the given `selection_fn` and `giving_clause_fn`
pub fn saturate(
    clauses: &Vec<CnfFormula>,
    selection_fn: &SelectionFunctionSignature,
    giving_clause_fn: GivingClauseSignature,
) -> Result<Substitution<CnfTerm>, LofError> {
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

/// Proof by saturation algorithm entrypoint. Proves `goals` from `premises`
/// by refutation: saturates the CNF of the premises together with the CNF
/// of the complemented goals until it derives the empty clause.
///
/// * `premises`: formulas assumed to hold, clausified as they are
/// * `goals`: formulas to prove, complemented before being clausified
/// * `selection_fn`: selects which literals of a clause may take part in
///   generating inferences
/// * `giving_clause_fn`: picks (and removes) the next clause to process from
///   the set of unprocessed clauses
/// * `track_answer`: whether to extend each goal clause with an answer literal,
///   so that the refutation also records the bindings of the goals' free variables
///
/// On a successful refutation returns the answer substitution, mapping each
/// free variable of the goals to the term witnessing it. If `track_answer` is
/// `false` no answer literal is ever introduced, so the returned substitution
/// is always empty. Returns an error if the set saturates without deriving
/// the empty clause (the goals don't follow from the premises), or if the
/// refutation only proves a disjunction of different answers.
pub fn saturation<F: ToCnfFormula + Complement>(
    premises: &[F],
    goals: &[F],
    selection_fn: &SelectionFunctionSignature,
    giving_clause_fn: GivingClauseSignature,
    track_answer: bool,
) -> Result<Substitution<CnfTerm>, LofError> {
    let mut saturation_set = vec![];

    for p in premises {
        saturation_set.extend(p.to_cnf());
    }
    for g in goals {
        for g in g.complement().to_cnf() {
            if track_answer {
                saturation_set.push(with_answer_literal(&g));
            } else {
                saturation_set.push(g);
            }
        }
    }

    saturate(&saturation_set, selection_fn, giving_clause_fn)
}

#[cfg(test)]
#[path = "../../tests/type_theory/algorithms/saturation.rs"]
mod tests;
