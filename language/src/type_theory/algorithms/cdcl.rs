use crate::error::LofError;
use crate::type_theory::algorithms::dpll::Model;
use crate::type_theory::grammars::cnf::CnfFormula::{self, Atom, Not};
use crate::type_theory::grammars::traits::{Complement, ToCnfFormula};
use std::collections::HashMap;

/// Factor by which atom activities decay at each conflict
const ACTIVITY_DECAY: f64 = 0.95;
/// Activity above which every activity gets rescaled, to avoid overflows
const ACTIVITY_LIMIT: f64 = 1e100;

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

    /// Position of the literal in tables indexed by literal, ie watch lists
    fn index(&self) -> usize {
        2 * self.atom + self.polarity as usize
    }
}

/// A disjunction of literals, the empty clause being ⊥
type Clause = Vec<Literal>;
/// Decided literal selection function signature, returns `None` when every
/// atom is assigned
type LiteralDecisionSignature = fn(&CdclState) -> Option<Literal>;

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
                // tautologies are already satisfied, watching them would only
                // slow down propagation
                continue;
            }

            for cnf_literal in cnf_clause.unpack_literals() {
                let (name, polarity) = match &cnf_literal {
                    Atom(name, args) if args.is_empty() => (name, true),
                    Not(inner) => match &**inner {
                        Atom(name, args) if args.is_empty() => (name, false),
                        _ => {
                            return Err(LofError::unsupported_construct(
                                "propositional CDCL",
                                &cnf_literal,
                            ));
                        }
                    },
                    _ => {
                        return Err(LofError::unsupported_construct(
                            "propositional CDCL",
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

/// Value of `literal` under `assignment`, `None` if its atom is unassigned
fn value(assignment: &[Option<bool>], literal: Literal) -> Option<bool> {
    assignment[literal.atom].map(|v| v == literal.polarity)
}

/// The state of a CDCL search: the clause database, the partial assignment
/// built so far and the bookkeeping needed to learn from its conflicts
struct CdclState {
    /// the input clauses with at least two literals, followed by the learned ones.
    /// Every clause watches its first two literals
    clauses: Vec<Clause>,
    /// for each literal, the clauses watching it
    watches: Vec<Vec<usize>>,
    assignment: Vec<Option<bool>>,
    /// decision level at which each atom got assigned
    levels: Vec<usize>,
    /// clause that implied each atom value, `None` for decisions and for
    /// unit clauses (input or learned), that hold at level 0
    reasons: Vec<Option<usize>>,
    /// assigned literals, in assignment order
    trail: Vec<Literal>,
    /// trail length at the start of each decision level
    trail_limits: Vec<usize>,
    /// trail position of the next literal to propagate
    propagated: usize,
    /// VSIDS score of each atom, ie how much it took part in recent conflicts
    activities: Vec<f64>,
    /// amount added to an atom activity when it takes part in a conflict
    bump: f64,
    /// last value of each atom, decisions reuse it (phase saving)
    saved_phases: Vec<bool>,
}
impl CdclState {
    /// Builds the initial state, with the unit clauses assigned at level 0.
    /// Returns `None` if `clauses` are trivially unsatisfiable, ie contain the
    /// empty clause or two complementary unit clauses
    fn new(atoms_count: usize, clauses: Vec<Clause>) -> Option<CdclState> {
        let mut state = CdclState {
            clauses: vec![],
            watches: vec![vec![]; 2 * atoms_count],
            assignment: vec![None; atoms_count],
            levels: vec![0; atoms_count],
            reasons: vec![None; atoms_count],
            trail: vec![],
            trail_limits: vec![],
            propagated: 0,
            activities: vec![0.0; atoms_count],
            bump: 1.0,
            saved_phases: vec![false; atoms_count],
        };

        for clause in clauses {
            match clause.len() {
                0 => return None,
                1 => match value(&state.assignment, clause[0]) {
                    Some(false) => return None,
                    Some(true) => {}
                    None => state.enqueue(clause[0], None),
                },
                _ => {
                    state.add_clause(clause);
                }
            }
        }

        Some(state)
    }

    fn decision_level(&self) -> usize {
        self.trail_limits.len()
    }

    /// Makes `literal` true at the current decision level, because of `reason`
    fn enqueue(&mut self, literal: Literal, reason: Option<usize>) {
        self.assignment[literal.atom] = Some(literal.polarity);
        self.levels[literal.atom] = self.decision_level();
        self.reasons[literal.atom] = reason;
        self.trail.push(literal);
    }

    /// Adds a clause with at least two literals to the database, watching its
    /// first two literals. Returns its index
    fn add_clause(&mut self, clause: Clause) -> usize {
        let index = self.clauses.len();
        self.watches[clause[0].index()].push(index);
        self.watches[clause[1].index()].push(index);
        self.clauses.push(clause);
        index
    }

    /// Unit propagation over the watched literals. For each literal made false
    /// since the last propagation, visits the clauses watching it, moving the
    /// watch to another non false literal, or else assigning the other watched
    /// literal (the clause became unit). Returns the clause falsified by the
    /// assignment, if any
    fn propagate(&mut self) -> Option<usize> {
        while self.propagated < self.trail.len() {
            let falsified = self.trail[self.propagated].negated();
            self.propagated += 1;
            // the watch moves to non false literals, never to `falsified`
            // itself, so its watch list can be taken while visiting it
            let mut watchers =
                std::mem::take(&mut self.watches[falsified.index()]);

            let mut i = 0;
            while i < watchers.len() {
                let clause_index = watchers[i];
                let clause = &mut self.clauses[clause_index];
                // keep the falsified watched literal in second position
                if clause[0] == falsified {
                    clause.swap(0, 1);
                }
                let other_watch = clause[0];

                // satisfied by the other watched literal
                if value(&self.assignment, other_watch) == Some(true) {
                    i += 1;
                    continue;
                }

                if let Some(k) = (2..clause.len()).find(|&k| {
                    value(&self.assignment, clause[k]) != Some(false)
                }) {
                    clause.swap(1, k);
                    self.watches[clause[1].index()].push(clause_index);
                    watchers.swap_remove(i);
                    continue;
                }

                // no replacement watch: every other literal is false
                i += 1;
                if value(&self.assignment, other_watch) == Some(false) {
                    self.watches[falsified.index()] = watchers;
                    return Some(clause_index);
                }
                self.enqueue(other_watch, Some(clause_index));
            }

            self.watches[falsified.index()] = watchers;
        }

        None
    }

    /// Increases the activity of `atom`, rescaling every activity if it grows
    /// too large
    fn bump_activity(&mut self, atom: usize) {
        self.activities[atom] += self.bump;
        if self.activities[atom] > ACTIVITY_LIMIT {
            for activity in self.activities.iter_mut() {
                *activity /= ACTIVITY_LIMIT;
            }
            self.bump /= ACTIVITY_LIMIT;
        }
    }

    /// Decays every activity, by growing the amount future bumps add instead,
    /// so that recent conflicts weigh more than older ones
    fn decay_activities(&mut self) {
        self.bump /= ACTIVITY_DECAY;
    }

    /// First UIP conflict analysis. Resolves the `conflict` clause with the
    /// reasons of its literals assigned at the current decision level, walking
    /// the trail backwards, until a single literal of the current level is left
    /// (the first unique implication point).
    /// Returns the learned clause, with the negated UIP first and a literal of
    /// the highest remaining level second, together with that level, ie the
    /// level to backjump to
    fn analyze(&mut self, conflict: usize) -> (Clause, usize) {
        let current_level = self.decision_level();
        let mut seen = vec![false; self.assignment.len()];
        let mut learned: Clause = vec![];
        // literals of the current level seen but not yet resolved upon
        let mut pending = 0;
        let mut clause_index = conflict;
        let mut trail_index = self.trail.len();

        let uip = loop {
            // the literal resolved upon is already seen, so it's skipped too
            for literal in self.clauses[clause_index].clone() {
                // level 0 literals are false in every model, drop them
                if seen[literal.atom] || self.levels[literal.atom] == 0 {
                    continue;
                }
                seen[literal.atom] = true;
                self.bump_activity(literal.atom);
                if self.levels[literal.atom] == current_level {
                    pending += 1;
                } else {
                    learned.push(literal);
                }
            }

            // current level literals follow every lower level one on the
            // trail, so this stops on a current level literal
            loop {
                trail_index -= 1;
                if seen[self.trail[trail_index].atom] {
                    break;
                }
            }
            let resolved = self.trail[trail_index];
            pending -= 1;
            if pending == 0 {
                break resolved;
            }
            clause_index = self.reasons[resolved.atom].expect(
                "current level literals other than the UIP are implied",
            );
        };

        learned.insert(0, uip.negated());
        let backjump_level = match (1..learned.len())
            .max_by_key(|&k| self.levels[learned[k].atom])
        {
            Some(k) => {
                learned.swap(1, k);
                self.levels[learned[1].atom]
            }
            None => 0,
        };

        (learned, backjump_level)
    }

    /// Undoes every assignment made above `level`, saving their phases
    fn backjump(&mut self, level: usize) {
        let limit = self.trail_limits[level];
        for literal in self.trail.drain(limit..) {
            self.assignment[literal.atom] = None;
            self.reasons[literal.atom] = None;
            self.saved_phases[literal.atom] = literal.polarity;
        }
        self.trail_limits.truncate(level);
        self.propagated = self.trail.len();
    }

    /// Adds the `learned` clause and assigns its first literal, the only one
    /// not false after backjumping
    fn learn(&mut self, learned: Clause) {
        if learned.len() == 1 {
            self.enqueue(learned[0], None);
        } else {
            let asserting = learned[0];
            let index = self.add_clause(learned);
            self.enqueue(asserting, Some(index));
        }
    }
}

/// Decides the unassigned atom with the highest activity (VSIDS), giving it
/// its last value. Atoms that recently took part in conflicts are the most
/// likely to lead to new ones, failing fast
fn decide_vsids(state: &CdclState) -> Option<Literal> {
    (0..state.assignment.len())
        .filter(|&atom| state.assignment[atom].is_none())
        .max_by(|&a, &b| state.activities[a].total_cmp(&state.activities[b]))
        .map(|atom| Literal {
            atom,
            polarity: state.saved_phases[atom],
        })
}

/// Core CDCL search. Applies unit propagation, and on each conflict learns a
/// clause by first UIP analysis and backjumps to the level where it becomes
/// unit, otherwise decides the literal returned by `decision_fn`.
/// Returns the satisfying assignment, if any
fn cdcl_search(
    mut state: CdclState,
    decision_fn: LiteralDecisionSignature,
) -> Option<Vec<Option<bool>>> {
    /// learns from a conflict and backjumps, a conflict at level 0 doesn't
    /// depend on any decision so the set is unsatisfiable
    macro_rules! conflict_analysis {
        ($conflict:expr) => {
            if state.decision_level() == 0 {
                return None;
            }
            let (learned, backjump_level) = state.analyze($conflict);
            state.backjump(backjump_level);
            state.learn(learned);
            state.decay_activities();
            // continue loop to propagate the learned clause literal
            continue;
        };
    }
    /// opens a new decision level with the decided literal, if every atom is
    /// assigned without conflicts every clause is satisfied
    macro_rules! decide {
        () => {
            let Some(decision) = decision_fn(&state) else {
                return Some(state.assignment);
            };
            state.trail_limits.push(state.trail.len());
            state.enqueue(decision, None);
        };
    }

    loop {
        if let Some(conflict) = state.propagate() {
            conflict_analysis!(conflict);
        }
        decide!();
    }
}

/// CDCL SAT solving algorithm. Returns a model for the conjunction of `formulas`
/// if satisfiable, `None` otherwise.
/// Fails if the clausified formulas contain non propositional literals,
/// ie atoms with arguments, equalities or quantifiers
pub fn cdcl<F: ToCnfFormula>(
    formulas: &[F],
) -> Result<Option<Model>, LofError> {
    let (atom_names, clauses) = preprocess(formulas)?;
    let assignment = CdclState::new(atom_names.len(), clauses)
        .and_then(|state| cdcl_search(state, decide_vsids));

    Ok(assignment.map(|assignment| {
        atom_names
            .into_iter()
            .zip(assignment)
            .map(|(name, value)| (name, value.unwrap_or(false)))
            .collect()
    }))
}

/// Proof by CDCL entrypoint. Proves `goals` from `premises` by refutation,
/// using the CDCL search algorithm.
/// Returns a `Some(countermodel)` if `goals` do not derive from `premises`,
/// `None` otherwise.
/// Fails if the clausified formulas contain non propositional literals,
/// ie atoms with arguments, equalities or quantifiers
pub fn cdcl_prove<F: ToCnfFormula + Complement>(
    premises: &[F],
    goals: &[F],
) -> Result<Option<Model>, LofError> {
    let mut refutation_set = vec![];
    for p in premises {
        refutation_set.extend(p.to_cnf());
    }
    for g in goals {
        refutation_set.extend(g.complement().to_cnf());
    }

    cdcl(&refutation_set)
}

#[cfg(test)]
#[path = "../../tests/type_theory/algorithms/cdcl.rs"]
mod tests;
