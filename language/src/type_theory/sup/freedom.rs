use super::sup::{
    SupFormula::{self, Equality, ForAll, Not},
    SupTerm::{self, Variable},
};
use crate::{config::GivingClause, type_theory::interface::Automatic};
use crate::{
    config::SelectionFunction::{self, All, Maximal},
    type_theory::sup::sup::Sup,
};
use std::cmp::Ordering::{Equal, Greater};

// ─── Literal selection ────────────────────────────────────────────────────────

/// Selection function to select a non-empty set of *literals* from a clause.
pub type SelectionFunctionSignature =
    Box<dyn Fn(&mut Vec<SupFormula>) -> Vec<SupFormula> + Send + Sync>;

pub fn get_selection_fn(
    selection_fn: SelectionFunction,
) -> SelectionFunctionSignature {
    Box::new(move |clause: &mut Vec<SupFormula>| match selection_fn {
        Maximal() => drop_maximal_literals(clause),
        All() => {
            let selected = clause.clone();
            *clause = vec![];
            selected
        }
    })
}

/// Given a list of literals of some clause, finds and removes all maximal literals
/// by the use of SUP simplification ordering
pub fn drop_maximal_literals(clause: &mut Vec<SupFormula>) -> Vec<SupFormula> {
    if clause.len() == 0 {
        return vec![];
    }

    let mut maximal = None;
    for literal in clause.iter() {
        match maximal.as_ref() {
            None => maximal = Some(literal.clone()),
            Some(current_max)
                if Sup::compare_types(literal, current_max) == Greater =>
            {
                maximal = Some(literal.clone());
            }
            _ => {}
        }
    }

    let maximal_formula = maximal.unwrap();
    let (maxes, rest): (Vec<_>, Vec<_>) = clause
        .drain(..)
        .partition(|f| Sup::compare_types(f, &maximal_formula) == Equal);
    *clause = rest;

    maxes
}
// ─── Given-clause strategy ────────────────────────────────────────────────────

/// Function signature for strategies that pick the next given clause to process
/// from the unprocessed set.
pub type GivingClauseSignature =
    fn(&mut Vec<SupFormula>) -> Result<SupFormula, String>;

pub fn get_giving_clause_fn(strategy: GivingClause) -> GivingClauseSignature {
    match strategy {
        GivingClause::Fifo => pick_clause,
        GivingClause::Weighted => pick_clause_weighted,
    }
}

fn clause_weight(φ: &SupFormula) -> usize {
    fn term_weight(t: &SupTerm) -> usize {
        match t {
            Variable(_) => 1,
            SupTerm::Application(_, args) => {
                1 + args.iter().map(term_weight).sum::<usize>()
            }
        }
    }
    fn formula_weight(φ: &SupFormula) -> usize {
        match φ {
            SupFormula::Atom(_, args) => {
                1 + args.iter().map(term_weight).sum::<usize>()
            }
            Equality(l, r) => 1 + term_weight(l) + term_weight(r),
            Not(inner) => 1 + formula_weight(inner),
            SupFormula::Clause(lits) => lits.iter().map(formula_weight).sum(),
            ForAll(_, ty, body) => {
                1 + formula_weight(ty) + formula_weight(body)
            }
        }
    }
    formula_weight(φ)
}

/// Picks the next clause FIFO (first in, first out).
pub fn pick_clause(
    clauses: &mut Vec<SupFormula>,
) -> Result<SupFormula, String> {
    Ok(clauses.remove(0))
}

/// Picks the lightest (shortest / shallowest) clause from the unprocessed set.
pub fn pick_clause_weighted(
    clauses: &mut Vec<SupFormula>,
) -> Result<SupFormula, String> {
    let min_idx = clauses
        .iter()
        .enumerate()
        .min_by_key(|(_, c)| clause_weight(c))
        .map(|(i, _)| i)
        .ok_or_else(|| "No clauses to pick".to_string())?;
    Ok(clauses.remove(min_idx))
}

#[cfg(test)]
mod tests {
    use crate::type_theory::sup::{
        freedom::drop_maximal_literals,
        sup::SupFormula::{Atom, Not},
    };

    #[test]
    fn test_maximal_literal_selection() {
        let constant_atom = Atom("P".to_string(), vec![]);
        let negated = Not(Box::new(constant_atom.clone()));
        let negated_renamed = Not(Box::new(Atom("Q".to_string(), vec![])));

        let mut test = vec![constant_atom.clone(), negated.clone()];
        assert_eq!(
            drop_maximal_literals(&mut test),
            vec![negated.clone()],
            "Maximal literal selection didnt pick the negated between 2 atoms"
        );
        assert_eq!(
            test,
            vec![constant_atom.clone()],
            "Maximal literal selection didnt remove the selected literal from input"
        );

        assert_eq!(
            drop_maximal_literals(&mut vec![
                constant_atom.clone(),
                negated.clone(),
                negated_renamed.clone()
            ]),
            vec![negated.clone(), negated_renamed.clone()],
            "Maximal literal selection didnt remove all maximal literals"
        );

        assert_eq!(
            drop_maximal_literals(&mut vec![]),
            vec![],
            "Maximal literal selection isnt working with empty clause"
        );
    }
}
