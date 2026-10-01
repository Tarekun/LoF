use crate::error::LofError;
use crate::type_theory::grammars::cnf::CnfFormula::{self, Atom, Not};
use crate::type_theory::grammars::traits::{Complement, ToCnfFormula};
use std::collections::HashMap;

/// A truth assignment over propositional atoms
pub type Model = HashMap<String, bool>;

/// A propositional literal, ie an (interned) atom together with its polarity
#[derive(Clone, Copy, Debug, PartialEq)]
struct Literal {
    atom: usize,
    polarity: bool,
}
impl Literal {
    fn negated(&self) -> Literal {
        Literal {
            atom: self.atom,
            polarity: !self.polarity,
        }
    }
}

/// A disjunction of literals, the empty clause being ⊥
type Clause = Vec<Literal>;
/// Decided literal selection function signature
type LiteralDecisionSignature = fn(&[Clause]) -> Literal;

fn preprocess<F: ToCnfFormula>(
    formulas: &[F],
) -> Result<(Vec<String>, Vec<Clause>), LofError> {
    let mut atom_names: Vec<String> = vec![];
    let mut atom_ids: HashMap<String, usize> = HashMap::new();
    let mut clauses = vec![];

    for formula in formulas {
        for cnf_clause in formula.to_cnf() {
            let mut clause: Clause = vec![];
            if cnf_clause.is_tautology() {
                // tautologies are already satisfied and there's no point on waiting
                // DPLL to detect them as such, better remove them to avoid causing
                // pointless backtracking on these
                continue;
            }

            for cnf_literal in cnf_clause.unpack_literals() {
                let (name, polarity) = match &cnf_literal {
                    Atom(name, args) if args.is_empty() => (name, true),
                    Not(inner) => match &**inner {
                        Atom(name, args) if args.is_empty() => (name, false),
                        _ => {
                            // TODO this is the source of Result signature of this module, see if can be avoided
                            return Err(LofError::unsupported_construct(
                                "propositional DPLL",
                                &cnf_literal,
                            ));
                        }
                    },
                    // TODO see if this should support equality too
                    _ => {
                        // TODO this is the source of Result signature of this module, see if can be avoided
                        return Err(LofError::unsupported_construct(
                            "propositional DPLL",
                            &cnf_literal,
                        ));
                    }
                };

                let next_id = atom_names.len();
                let atom =
                    *atom_ids.entry(name.to_string()).or_insert_with(|| {
                        atom_names.push(name.to_string());
                        next_id
                    });
                let literal = Literal { atom, polarity };

                if !clause.contains(&literal) {
                    clause.push(literal);
                }
            }
            clauses.push(clause);
        }
    }

    Ok((atom_names, clauses))
}

/// Returns the literals whose atom occurs in `clauses` with one polarity only
fn pure_literals(clauses: &[Clause], atoms_count: usize) -> Vec<Literal> {
    // (occurs positively, occurs negatively) for each atom
    let mut occurrences = vec![(false, false); atoms_count];
    for literal in clauses.iter().flatten() {
        if literal.polarity {
            occurrences[literal.atom].0 = true;
        } else {
            occurrences[literal.atom].1 = true;
        }
    }

    occurrences
        .into_iter()
        .enumerate()
        .filter_map(|(atom, occurrence)| match occurrence {
            (true, false) => Some(Literal {
                atom,
                polarity: true,
            }),
            (false, true) => Some(Literal {
                atom,
                polarity: false,
            }),
            _ => None,
        })
        .collect()
}

/// Decides the first literal of the shortest clause (the shortest clause is
/// the most likely to become empty, failing fast)
fn decide_shortest_clause(clauses: &[Clause]) -> Literal {
    clauses
        .iter()
        .min_by_key(|clause| clause.len())
        .expect("decisions are only taken on a non empty list of clauses")[0]
}

/// Makes `literal` true: records it in `assignment` and simplifies `clauses`
/// in place, dropping the clauses it satisfies and removing its complement
/// from the remaining ones
fn assign(
    clauses: &mut Vec<Clause>,
    assignment: &mut Vec<Option<bool>>,
    literal: Literal,
) {
    assignment[literal.atom] = Some(literal.polarity);
    clauses.retain(|clause| !clause.contains(&literal));
    for clause in clauses.iter_mut() {
        clause.retain(|l| *l != literal.negated());
    }
}

/// Core DPLL search. Applies unit propagation and optionally pure literal
/// elimination, then decides the literal returned by `decision_fn`.
/// Returns the satisfying (partial) assignment extending `assignment`, if any
fn dpll_search(
    mut clauses: Vec<Clause>,
    mut assignment: Vec<Option<bool>>,
    decision_fn: LiteralDecisionSignature,
    decide_pures: bool,
) -> Option<Vec<Option<bool>>> {
    /// if an empty clause () is reached, the set is unsatisfiable
    macro_rules! unsat_detection {
        () => {
            if clauses.iter().any(|clause| clause.is_empty()) {
                return None;
            }
        };
    }
    /// finds a unit literal and iterates it over clauses for unit propagation
    macro_rules! unit_propagation {
        () => {
            if let Some(unit_literal) =
                clauses.iter().find(|c| c.len() == 1).map(|c| c[0])
            {
                assign(&mut clauses, &mut assignment, unit_literal);
                // continue loop to retry unsat_detection/unit_propagation
                continue;
            }
        };
    }
    /// pure literals can be assigned satisfing some clauses they appear in
    /// without constraining clauses they dont appear in
    macro_rules! pures_elimination {
        () => {
            let pures = pure_literals(&clauses, assignment.len());
            if pures.is_empty() {
                break;
            }
            for pure in pures {
                assign(&mut clauses, &mut assignment, pure);
            }
        };
    }
    /// decides a literal and recurs, with backtracking for opposite decision
    macro_rules! decide {
        () => {
            let decision = decision_fn(&clauses);
            for literal in [decision, decision.negated()] {
                let mut branch_clauses = clauses.clone();
                let mut branch_assignment = assignment.clone();
                assign(&mut branch_clauses, &mut branch_assignment, literal);
                if let Some(model) = dpll_search(
                    branch_clauses,
                    branch_assignment,
                    decision_fn,
                    decide_pures,
                ) {
                    return Some(model);
                }
            }
        };
    }

    loop {
        unsat_detection!();
        unit_propagation!();
        if decide_pures {
            pures_elimination!();
        } else {
            break;
        }
    }

    // every clause is satisfied
    if clauses.is_empty() {
        return Some(assignment);
    }
    decide!();

    // if recursive calls of decide! didnt return it's so over
    None
}

/// DPLL SAT solving algorithm. Returns a model for the conjunction of `formulas`
/// if satisfiable, `None` otherwise.
/// Fails if the clausified formulas contain non propositional literals,
/// ie atoms with arguments, equalities or quantifiers
pub fn dpll<F: ToCnfFormula>(
    formulas: &[F],
) -> Result<Option<Model>, LofError> {
    let (atom_names, clauses) = preprocess(formulas)?;
    let assignment = dpll_search(
        clauses,
        vec![None; atom_names.len()],
        decide_shortest_clause,
        true,
    );

    Ok(assignment.map(|assignment| {
        atom_names
            .into_iter()
            .zip(assignment)
            .map(|(name, value)| (name, value.unwrap_or(false)))
            .collect()
    }))
}

/// Proof by DPLL entrypoint. Proves `goals` from `premises` by refutation,
/// using the DPLL search algorithm.
/// Returns a `Some(countermodel)` if `goals` do not derive from `premises`,
/// `None` otherwise.
/// Fails if the clausified formulas contain non propositional literals,
/// ie atoms with arguments, equalities or quantifiers
pub fn dpll_prove<F: ToCnfFormula + Complement>(
    premises: &[F],
    goals: &[F],
) -> Result<Option<Model>, LofError> {
    let mut refutation_set: Vec<CnfFormula> = vec![];
    for p in premises {
        refutation_set.extend(p.to_cnf());
    }
    for g in goals {
        refutation_set.extend(g.complement().to_cnf());
    }

    dpll(&refutation_set)
}

#[cfg(test)]
#[path = "../../tests/type_theory/algorithms/dpll.rs"]
mod tests;
