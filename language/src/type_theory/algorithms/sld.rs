use crate::error::LofError;
use crate::type_theory::commons::unification::Substitution;
use crate::type_theory::grammars::cnf::CnfFormula::{self, Atom, Not};
use crate::type_theory::grammars::cnf::CnfTerm::{self, Variable};
use crate::type_theory::grammars::traits::{ToCnfFormula, Unification};

/// A definite Horn clause `head :- body1,...,bodyN`.
/// Since this is supposed to be used during SLD search only
/// it requires an head to be present
#[derive(Clone, Debug, PartialEq)]
struct HornClause {
    head: CnfFormula,
    body: Vec<CnfFormula>,
}

/// Checks that `clause` is a definite Horn clause (exactly one positive
/// literal, any number of negative ones, every literal a plain atom) and
/// splits it into its head and body.
fn to_horn_clause(clause: &CnfFormula) -> Result<HornClause, LofError> {
    let mut head = None;
    let mut body = vec![];

    for literal in clause.unpack_literals() {
        match literal {
            Atom(name, args) => {
                if head.is_some() {
                    return Err(LofError::custom(format!(
                        "clause {:?} is not a Horn clause: it has more than one positive literal",
                        clause
                    )));
                }
                head = Some(Atom(name, args));
            }
            Not(inner) => match *inner {
                Atom(name, args) => body.push(Atom(name, args)),
                other => {
                    return Err(LofError::custom(format!(
                        "SLD only supports negated atoms as body literals, found ¬{:?} in clause {:?}",
                        other, clause
                    )));
                }
            },
            other => {
                return Err(LofError::custom(format!(
                    "literal {:?} in clause {:?} isn't supported by SLD (only atoms and their negations are)",
                    other, clause
                )));
            }
        }
    }

    head.map(|head| HornClause { head, body }).ok_or_else(|| {
        LofError::custom(format!(
            "clause {:?} has no positive literal: SLD program clauses must be definite (headed) Horn clauses",
            clause
        ))
    })
}

/// Checks each program clause is a definite Horn clause, producing the SLD
/// program (the clause database).
fn preprocess_program<F: ToCnfFormula>(
    clauses: &[F],
) -> Result<Vec<HornClause>, LofError> {
    let mut cnf_program = vec![];
    for p in clauses {
        cnf_program.extend(p.to_cnf());
    }

    cnf_program.iter().map(to_horn_clause).collect()
}

/// Checks each goal clause is a single atom and returns the initial list
/// of subgoals `g1,...,gn` to solve left to right.
fn preprocess_goals<F: ToCnfFormula>(
    clauses: &[F],
) -> Result<Vec<CnfFormula>, LofError> {
    let mut cnf_goals = vec![];
    for g in clauses {
        cnf_goals.extend(g.to_cnf());
    }

    cnf_goals
        .iter()
        .map(|clause| {
            let horn = to_horn_clause(clause)?;
            if !horn.body.is_empty() {
                return Err(LofError::custom(format!(
                    "goal {:?} isn't a plain atomic subgoal: SLD goals must be atoms",
                    clause
                )));
            }
            Ok(horn.head)
        })
        .collect()
}

/// Renames a clause's variables apart with a fresh, globally unique suffix
fn freshen_clause(clause: &HornClause) -> HornClause {
    let mut literals = vec![clause.head.clone()];
    literals
        .extend(clause.body.iter().cloned().map(|atom| Not(Box::new(atom))));

    let renamed = CnfFormula::Clause(literals).standardize_apart();
    to_horn_clause(&renamed).expect(
        "standardize_apart only renames variables, it can't break Horn-ness",
    )
}

/// Core backtracking SLD search. Tries to solve `goals` left to right against
/// `program`, on success calling `on_success` with the fully-reduced answer
/// substitution. `on_success` returning `true` stops the search, returning
/// `false` makes the search backtrack and keep looking for further solutions
fn sld_derive(
    goals: &[CnfFormula],
    subst: &Substitution<CnfTerm>,
    program: &[HornClause],
    on_success: &mut dyn FnMut(Substitution<CnfTerm>) -> bool,
) -> bool {
    let Some((goal, rest)) = goals.split_first() else {
        let solution = subst.clone().reduce(|term, var_name, arg| {
            term.substitute_term(&Variable(var_name.to_string()), arg)
        });
        return on_success(solution);
    };

    let goal = goal.apply_substitution(subst);

    for clause in program {
        let candidate = freshen_clause(clause);
        let Ok(mgu) = goal.unifies(&candidate.head) else {
            // this clause's head doesn't match the goal -> try the next one
            continue;
        };

        let mut extended_subst = subst.clone();
        extended_subst.merge(mgu);
        let mut next_goals = candidate.body;
        next_goals.extend(rest.iter().cloned());

        if sld_derive(&next_goals, &extended_subst, program, on_success) {
            return true;
        }
    }

    false
}

/// Finds the first SLD solution of `goals` from the definite Horn
/// clauses in `program`, if any
pub fn sld_prove_first<F: ToCnfFormula>(
    program: &[F],
    goals: &[F],
) -> Result<Substitution<CnfTerm>, LofError> {
    let program = preprocess_program(program)?;
    let goals = preprocess_goals(goals)?;

    let mut solution = None;
    sld_derive(&goals, &Substitution::empty(), &program, &mut |subst| {
        solution = Some(subst);
        true
    });

    if let Some(solution) = solution {
        Ok(solution)
    } else {
        return Err(LofError::custom(
            "Couldn't find a solution for the goals with SLD resolution",
        ));
    }
}

/// Finds every SLD solution of `goals` from the definite Horn
/// clauses in `program`
pub fn sld_prove_all<F: ToCnfFormula>(
    program: &[F],
    goals: &[F],
) -> Result<Vec<Substitution<CnfTerm>>, LofError> {
    let program = preprocess_program(program)?;
    let goals = preprocess_goals(goals)?;

    let mut solutions = vec![];
    sld_derive(&goals, &Substitution::empty(), &program, &mut |subst| {
        solutions.push(subst);
        false
    });

    if !solutions.is_empty() {
        Ok(solutions)
    } else {
        return Err(LofError::custom(
            "Couldn't find a solution for the goals with SLD resolution",
        ));
    }
}

#[cfg(test)]
#[path = "../../tests/type_theory/algorithms/sld.rs"]
mod tests;
