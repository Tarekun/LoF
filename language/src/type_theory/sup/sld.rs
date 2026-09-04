//! SLD resolution, the proof procedure behind Prolog: it works exclusively on
//! Horn clauses `h :- g1,...,gn` (at most one positive literal) and, unlike
//! saturation, never needs to invent new clauses. Solving `h` just means
//! solving every subgoal `g1,...,gn` in turn, backtracking to the next
//! candidate clause whenever a subgoal has no (further) solution.
//!
//! This module reuses the existing FOL clausification pipeline (`clausify`,
//! `term_to_sup`) to get down to `SupFormula` clauses, then layers a Horn
//! check and a small backtracking search engine on top.

use crate::error::LofError;
use crate::type_theory::commons::unification::Substitution;
use crate::type_theory::fol::fol::FolFormula;
use crate::type_theory::fol::fol_utils::clausify;
use crate::type_theory::sup::sup::{
    SupFormula::{self, Atom, Not},
    SupTerm::{self, Variable},
};
use crate::type_theory::sup::sup_utils::{standardize_apart, substitute_term, unpack_literals};
use crate::type_theory::sup::unification::{formula_apply_substitution, formulas_unify};
use std::collections::HashSet;

/// A definite Horn clause `head :- body1,...,bodyN` (`body` empty means a fact).
/// Unlike general Horn clauses, `head` is mandatory here: this module only ever
/// needs the two roles SLD actually has for clauses, program rules/facts
/// (always headed) and query goals (modeled separately as bare atoms), so a
/// headless (all-negative) clause is rejected rather than represented.
#[derive(Clone, Debug, PartialEq)]
pub struct HornClause {
    pub head: SupFormula,
    pub body: Vec<SupFormula>,
}

/// Checks that `clause` is a definite Horn clause (exactly one positive
/// literal, any number of negative ones, every literal a plain atom) and
/// splits it into its head and body.
pub fn to_horn_clause(clause: &SupFormula) -> Result<HornClause, LofError> {
    let mut head = None;
    let mut body = vec![];

    for literal in unpack_literals(clause) {
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

/// Clausifies each assumption and checks the result is a definite Horn
/// clause, producing the SLD program (the clause database).
pub fn preprocess_assumptions(
    assumptions: &[FolFormula],
    constants: &HashSet<String>,
) -> Result<Vec<HornClause>, LofError> {
    let mut program = vec![];
    for assumption in assumptions {
        for clause in clausify(assumption, constants)? {
            program.push(to_horn_clause(&clause)?);
        }
    }
    Ok(program)
}

/// Clausifies each goal and checks the result is a single atom (a query
/// can't have a body: it's the thing to be solved, not a rule), producing
/// the initial list of subgoals `g1,...,gn` to solve left to right.
pub fn preprocess_goals(
    goals: &[FolFormula],
    constants: &HashSet<String>,
) -> Result<Vec<SupFormula>, LofError> {
    let mut subgoals = vec![];
    for goal in goals {
        for clause in clausify(goal, constants)? {
            let horn = to_horn_clause(&clause)?;
            if !horn.body.is_empty() {
                return Err(LofError::custom(format!(
                    "goal {:?} isn't a plain atomic subgoal: SLD goals must be atoms",
                    clause
                )));
            }
            subgoals.push(horn.head);
        }
    }
    Ok(subgoals)
}

/// Renames a clause's variables apart with a fresh, globally unique suffix.
/// Every *use* of a program clause during the search needs its own fresh
/// copy, otherwise two uses of the same recursive rule would share
/// variables and corrupt each other's bindings.
fn freshen_clause(clause: &HornClause) -> HornClause {
    let mut literals = vec![clause.head.clone()];
    literals.extend(clause.body.iter().cloned().map(|atom| Not(Box::new(atom))));

    let renamed = standardize_apart(&SupFormula::Clause(literals));
    to_horn_clause(&renamed)
        .expect("standardize_apart only renames variables, it can't break Horn-ness")
}

/// Core backtracking SLD search. Tries to solve `goals` left to right against
/// `program`, on success calling `on_success` with the fully-reduced answer
/// substitution. `on_success` returning `true` stops the whole search
/// (short-circuiting all pending alternatives); returning `false` makes the
/// search backtrack and keep looking for further solutions. The return value
/// mirrors that: `true` iff the search was stopped early by `on_success`.
fn sld_derive(
    goals: &[SupFormula],
    subst: &Substitution<SupTerm>,
    program: &[HornClause],
    on_success: &mut dyn FnMut(&Substitution<SupTerm>) -> bool,
) -> bool {
    let Some((goal, rest)) = goals.split_first() else {
        let solution = subst.clone().reduce(|term, var_name, arg| {
            substitute_term(term, &Variable(var_name.to_string()), arg)
        });
        return on_success(&solution);
    };

    let goal = formula_apply_substitution(goal, subst);

    for clause in program {
        let candidate = freshen_clause(clause);
        let Ok(mgu) = formulas_unify(&goal, &candidate.head) else {
            // this clause's head doesn't match the goal: try the next one
            continue;
        };

        let mut extended_subst = subst.clone();
        extended_subst.merge(mgu);

        let mut next_goals = candidate.body;
        next_goals.extend(rest.iter().cloned());

        if sld_derive(&next_goals, &extended_subst, program, on_success) {
            return true;
        }
        // that clause led to a dead end (or the caller wants more answers):
        // backtrack and try the next candidate clause
    }

    false
}

/// Finds the first SLD proof of `goals` from `program`, if any.
pub fn sld_prove_first(
    program: &[HornClause],
    goals: &[SupFormula],
) -> Option<Substitution<SupTerm>> {
    let mut solution = None;
    sld_derive(goals, &Substitution::empty(), program, &mut |subst| {
        solution = Some(subst.clone());
        true
    });
    solution
}

/// Finds every SLD proof of `goals` from `program`, exploring every
/// backtracking alternative (may not terminate if the program admits
/// infinitely many proofs).
pub fn sld_prove_all(
    program: &[HornClause],
    goals: &[SupFormula],
) -> Vec<Substitution<SupTerm>> {
    let mut solutions = vec![];
    sld_derive(goals, &Substitution::empty(), program, &mut |subst| {
        solutions.push(subst.clone());
        false
    });
    solutions
}

/// Full FOL -> SLD pipeline: clausifies `assumptions` into a Horn-clause
/// program, clausifies `goals` into a list of subgoals, and runs SLD
/// resolution to find a single proof (and the substitution witnessing it).
pub fn sld_solve(
    assumptions: &[FolFormula],
    goals: &[FolFormula],
    constants: &HashSet<String>,
) -> Result<Substitution<SupTerm>, LofError> {
    let program = preprocess_assumptions(assumptions, constants)?;
    let query = preprocess_goals(goals, constants)?;

    sld_prove_first(&program, &query).ok_or_else(|| {
        LofError::custom(
            "SLD resolution failed: couldn't derive the goal(s) from the given assumptions",
        )
    })
}

/// Same as [`sld_solve`], but collects every proof found by backtracking
/// through all alternatives instead of stopping at the first one.
pub fn sld_solve_all(
    assumptions: &[FolFormula],
    goals: &[FolFormula],
    constants: &HashSet<String>,
) -> Result<Vec<Substitution<SupTerm>>, LofError> {
    let program = preprocess_assumptions(assumptions, constants)?;
    let query = preprocess_goals(goals, constants)?;

    Ok(sld_prove_all(&program, &query))
}

#[cfg(test)]
mod unit_tests {
    use super::*;
    use crate::type_theory::fol::fol::{
        FolFormula::{Arrow, Conjunction, Disjunction, Not as FolNot, Predicate},
        FolTerm::{self, Variable as FolVar},
    };
    use crate::type_theory::fol::fol_utils::make_multiarg_app;
    use crate::type_theory::sup::sup::{
        SupFormula::{Clause, Equality},
        SupTerm::Application,
    };

    //########################### TEST HELPERS
    fn v(name: &str) -> FolTerm {
        FolVar(name.to_string())
    }
    fn c(name: &str, args: &[FolTerm]) -> FolTerm {
        make_multiarg_app(name, args)
    }
    fn p(name: &str, args: &[FolTerm]) -> FolFormula {
        Predicate(name.to_string(), args.to_vec())
    }
    /// A fact is just its head, a rule is `head :- body1,...,bodyN`
    fn rule(head: FolFormula, body: Vec<FolFormula>) -> FolFormula {
        if body.is_empty() {
            head
        } else {
            Arrow(Box::new(Conjunction(body)), Box::new(head))
        }
    }
    fn constants(names: &[&str]) -> HashSet<String> {
        names.iter().map(|s| s.to_string()).collect()
    }
    fn atom(name: &str) -> SupTerm {
        Application(name.to_string(), vec![])
    }
    //########################### TEST HELPERS

    #[test]
    fn test_to_horn_clause_accepts_facts_and_rules() {
        let p = SupFormula::Atom("p".to_string(), vec![]);
        let q = SupFormula::Atom("q".to_string(), vec![]);

        let fact =
            to_horn_clause(&p).expect("a bare atom is a valid (fact) Horn clause");
        assert_eq!(fact.head, p);
        assert!(fact.body.is_empty());

        let rule_clause = Clause(vec![p.clone(), Not(Box::new(q.clone()))]);
        let rule = to_horn_clause(&rule_clause)
            .expect("one positive + one negative literal is a valid Horn clause");
        assert_eq!(rule.head, p);
        assert_eq!(rule.body, vec![q]);
    }

    #[test]
    fn test_to_horn_clause_rejects_non_horn_and_headless_clauses() {
        let p = SupFormula::Atom("p".to_string(), vec![]);
        let q = SupFormula::Atom("q".to_string(), vec![]);

        let two_positive = Clause(vec![p.clone(), q.clone()]);
        assert!(
            to_horn_clause(&two_positive).is_err(),
            "a clause with 2 positive literals isn't a Horn clause"
        );

        let headless = Clause(vec![Not(Box::new(p.clone())), Not(Box::new(q.clone()))]);
        assert!(
            to_horn_clause(&headless).is_err(),
            "SLD program clauses need exactly one positive literal (a head)"
        );

        let with_equality =
            Equality(SupTerm::Variable("x".to_string()), SupTerm::Variable("y".to_string()));
        assert!(
            to_horn_clause(&with_equality).is_err(),
            "equality literals aren't supported by this SLD implementation"
        );
    }

    #[test]
    fn test_preprocess_assumptions_rejects_non_horn_formula() {
        let x = v("x");
        let not_horn = Disjunction(vec![p("P", &[x.clone()]), p("Q", &[x])]);

        assert!(
            preprocess_assumptions(&[not_horn], &HashSet::new()).is_err(),
            "a disjunction of two positive predicates isn't a Horn clause and should be rejected"
        );
    }

    #[test]
    fn test_preprocess_goals_rejects_non_atomic_goal() {
        let goal = FolNot(Box::new(p("P", &[v("x")])));

        assert!(
            preprocess_goals(&[goal], &HashSet::new()).is_err(),
            "SLD goals must be plain atoms; a negated goal should be rejected"
        );
    }

    #[test]
    fn test_sld_backtracks_across_failing_facts() {
        // likes(mary, wine).
        // likes(mary, cheese).
        // ?- likes(mary, cheese).
        let assumptions = vec![
            rule(p("likes", &[c("mary", &[]), c("wine", &[])]), vec![]),
            rule(p("likes", &[c("mary", &[]), c("cheese", &[])]), vec![]),
        ];
        let goals = vec![p("likes", &[c("mary", &[]), c("cheese", &[])])];
        let constants = constants(&["mary", "wine", "cheese"]);

        assert!(
            sld_solve(&assumptions, &goals, &constants).is_ok(),
            "SLD should backtrack past the first non-unifying fact and succeed on the second"
        );
    }

    #[test]
    fn test_sld_solves_for_free_variable() {
        // parent(tom, bob).
        // ?- parent(tom, X).
        let assumptions = vec![rule(p("parent", &[c("tom", &[]), c("bob", &[])]), vec![])];
        let goals = vec![p("parent", &[c("tom", &[]), v("X")])];
        let constants = constants(&["tom", "bob"]);

        let solution = sld_solve(&assumptions, &goals, &constants)
            .expect("parent(tom,bob) should let SLD solve parent(tom,X) with X=bob");
        assert_eq!(solution.resolvent("X"), Some(&atom("bob")));
    }

    #[test]
    fn test_sld_solve_fails_when_goal_isnt_entailed() {
        // likes(john, wine).
        // ?- likes(mary, X).
        let assumptions = vec![rule(p("likes", &[c("john", &[]), c("wine", &[])]), vec![])];
        let goals = vec![p("likes", &[c("mary", &[]), v("X")])];
        let constants = constants(&["john", "mary", "wine"]);

        assert!(
            sld_solve(&assumptions, &goals, &constants).is_err(),
            "SLD shouldn't find a proof for a goal that isn't entailed by the assumptions"
        );
    }

    #[test]
    fn test_sld_recursive_rule_arithmetic() {
        // add(zero, x, x).
        // add(s(n), m, s(p)) :- add(n, m, p).
        // ?- add(s(s(zero)), s(zero), R).
        let zero = || c("zero", &[]);
        let s = |t: FolTerm| c("s", &[t]);

        let assumptions = vec![
            rule(p("add", &[zero(), v("x"), v("x")]), vec![]),
            rule(
                p("add", &[s(v("n")), v("m"), s(v("p"))]),
                vec![p("add", &[v("n"), v("m"), v("p")])],
            ),
        ];
        let goals = vec![p("add", &[s(s(zero())), s(zero()), v("R")])];
        let constants = constants(&["zero", "s"]);

        let solution = sld_solve(&assumptions, &goals, &constants)
            .expect("SLD should derive 2+1=3 from the Peano add rules");

        let three = Application(
            "s".to_string(),
            vec![Application(
                "s".to_string(),
                vec![Application("s".to_string(), vec![atom("zero")])],
            )],
        );
        assert_eq!(solution.resolvent("R"), Some(&three));
    }

    #[test]
    fn test_sld_finds_all_solutions_via_backtracking() {
        // member(x, cons(x, rest)).
        // member(x, cons(first, rest)) :- member(x, rest).
        // ?- member(X, cons(a, cons(b, cons(c, nil)))).
        let nil = || c("nil", &[]);
        let cons = |h: FolTerm, t: FolTerm| c("cons", &[h, t]);

        let list = cons(c("a", &[]), cons(c("b", &[]), cons(c("c", &[]), nil())));

        let assumptions = vec![
            rule(p("member", &[v("x"), cons(v("x"), v("rest"))]), vec![]),
            rule(
                p("member", &[v("x"), cons(v("first"), v("rest"))]),
                vec![p("member", &[v("x"), v("rest")])],
            ),
        ];
        let goals = vec![p("member", &[v("X"), list])];
        let constants = constants(&["a", "b", "c", "nil", "cons"]);

        let solutions = sld_solve_all(&assumptions, &goals, &constants)
            .expect("preprocessing should succeed for a valid Horn program");

        let found: Vec<_> =
            solutions.iter().map(|subst| subst.resolvent("X").cloned()).collect();
        assert_eq!(
            found,
            vec![Some(atom("a")), Some(atom("b")), Some(atom("c"))],
            "SLD should backtrack through both member clauses to enumerate every list element"
        );
    }
}
