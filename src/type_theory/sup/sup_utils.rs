use super::sup::{
    Sup,
    SupFormula::{self, Atom, Clause, Equality, ForAll, Not},
    SupTerm::{self, Application, Variable},
};
use crate::{
    config::SelectionFunction::{self, All, Maximal},
    type_theory::interface::{Automatic, TypeTheory},
};
use std::cmp::Ordering::{self, Equal, Greater, Less};

/// Returns the ordered vector of formal argument types of nested universal quantification
pub fn get_arg_types(forall: &SupFormula) -> Vec<SupFormula> {
    match forall {
        ForAll(_, var_type, body) => {
            let mut result = vec![*var_type.clone()];
            let rest = get_arg_types(&body);
            result.extend(rest);
            result
        }
        _ => vec![],
    }
}

/// Returns the innermost formula of nested universal quantification
pub fn get_forall_innermost(forall: &SupFormula) -> SupFormula {
    match forall {
        ForAll(_, _, body) => get_forall_innermost(&body),
        _ => forall.to_owned(),
    }
}

/// Check if two literals are (syntactically) complements
fn are_complements(l1: &SupFormula, l2: &SupFormula) -> bool {
    match (l1, l2) {
        (Atom(_, _), Not(q)) => **q == *l1,
        (Not(p), Atom(_, _)) => **p == *l2,
        _ => false,
    }
}

/// Returns `true` if the formula is *found* to be a tautology, but who knows...
pub fn is_tautology(φ: &SupFormula) -> bool {
    //body...
    match φ {
        //TODO look for axioms/sorts?
        Clause(literals) => {
            for (idx, lit) in literals.iter().enumerate() {
                if is_tautology(lit) {
                    return true;
                }

                // excluded middle
                for lit2 in &literals[0..idx] {
                    if are_complements(lit, lit2) {
                        return true;
                    }
                }
            }

            false
        }
        // identity of equals
        Equality(left, right) => Sup::base_term_equality(left, right).is_ok(),

        // TODO review
        _ => false,
    }
}

/// Implements standard Knuth-Bendix ordering of terms
pub fn kbo_terms(term1: &SupTerm, term2: &SupTerm) -> Ordering {
    fn weight(term: &SupTerm) -> i32 {
        match term {
            Variable(_) => 1,
            Application(_, args) => 1 + (args.len() as i32),
        }
    }

    let w1 = weight(term1);
    let w2 = weight(term2);
    if w1 != w2 {
        return w1.cmp(&w2);
    }

    // in case terms have the same weight
    match (term1, term2) {
        (Variable(_), Variable(_)) => Equal,
        // (Variable(name1), Variable(name2)) => name1.cmp(name2),
        (Variable(_), Application(_, _)) => Less,
        (Application(_, _), Variable(_)) => Greater,
        (Application(_, args1), Application(_, args2)) => {
            match args1.len().cmp(&args2.len()) {
                Ordering::Equal => {
                    for (argl, argr) in args1.iter().zip(args2.iter()) {
                        match kbo_terms(argl, argr) {
                            Ordering::Equal => continue,
                            non_eq => return non_eq,
                        }
                    }
                    Equal
                }
                non_eq => non_eq,
            }
        }
    }
}
pub fn kbo_types(φ1: &SupFormula, φ2: &SupFormula) -> Ordering {
    match (φ1, φ2) {
        (Atom(_, args1), Atom(_, args2)) => {
            match args1.len().cmp(&args2.len()) {
                Equal => {
                    for (a1, a2) in args1.iter().zip(args2.iter()) {
                        match kbo_terms(a1, a2) {
                            Equal => continue,
                            non_eq => return non_eq,
                        }
                    }
                    Equal
                    // p1.cmp(&p2)
                }
                non_eq => non_eq,
            }
        }
        (Not(psi1), Not(psi2)) => kbo_types(psi1, psi2),
        (Equality(left1, right1), Equality(left2, right2)) => {
            match kbo_terms(left1, left2) {
                Equal => kbo_terms(right1, right2),
                not_eq => not_eq,
            }
        }
        (Clause(lit1), Clause(lit2)) => {
            if lit1.len().cmp(&lit2.len()) != Equal {
                return lit1.len().cmp(&lit2.len());
            }

            let mut c1_sorted = lit1.clone();
            let mut c2_sorted = lit2.clone();
            c1_sorted.sort_by(kbo_types);
            c2_sorted.sort_by(kbo_types);

            for (a, b) in c1_sorted.iter().zip(c2_sorted.iter()) {
                match kbo_types(a, b) {
                    Ordering::Equal => continue,
                    non_eq => return non_eq,
                }
            }
            Equal
        }
        (ForAll(_, _, body1), ForAll(_, _, body2)) => {
            kbo_types(body1, body2)
            // TODO: revise this
            // match kbo_types(body1, body2) {
            //     Equal => v1.cmp(v2),
            //     non_eq => non_eq,
            // }
        }

        // order formulas by constructor kind if they are different
        (Atom(_, _), _) => Ordering::Less,
        (_, Atom(_, _)) => Ordering::Greater,
        (Not(_), _) => Ordering::Less,
        (_, Not(_)) => Ordering::Greater,
        (Equality(_, _), _) => Ordering::Less,
        (_, Equality(_, _)) => Ordering::Greater,
        (Clause(_), _) => Ordering::Less,
        (_, Clause(_)) => Ordering::Greater,
    }
}

#[allow(non_snake_case)]
/// Checks wheter clause `C` subsumes `D`, ie if `C`≐`E` where `E` is a subset
/// of literals of `D`
pub fn subsumes(C: &SupFormula, D: &SupFormula) -> bool {
    let Clause(c_lits) = C else { return false };
    let Clause(d_lits) = D else { return false };

    // TODO if i implement Eq and Hash for SupFormula in a way that supports
    // alpha equivalence this time complexity can be reduced from O(nm) to O(n+m)
    c_lits.iter().all(|c_lit| {
        d_lits
            .iter()
            //TODO currently this is syntactic equality with no mgu support
            .any(|d_lit| Sup::base_type_equality(c_lit, d_lit).is_ok())
    })
}

#[allow(non_snake_case)]
/// Given a clause formula, returns the vector of its literals.
/// Treats literal variants as singleton clauses
pub fn unpack_literals(C: &SupFormula) -> Result<Vec<SupFormula>, String> {
    match C {
        Clause(literals) => Ok(literals.to_owned()),
        _ => Ok(vec![C.clone()]),
    }
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

/// Returns a new term identical to `term` where every occurance of `target` is
/// substituted by `arg`
pub fn substitute_term(
    term: &SupTerm,
    target: &SupTerm,
    arg: &SupTerm,
) -> SupTerm {
    if Sup::base_term_equality(term, target).is_ok() {
        return arg.to_owned();
    }
    match term {
        Application(fun_name, fun_args) => Application(
            fun_name.to_string(),
            fun_args
                .iter()
                .map(|fun_arg| substitute_term(fun_arg, target, arg))
                .collect(),
        ),
        // non-recursive cases didnt pass equality against `target` by now
        _ => term.to_owned(),
    }
}
/// Returns a new formula identical to `formula` where every occurance of `target` is
/// substituted by `arg`
pub fn substitute_formula(
    formula: &SupFormula,
    target: &SupTerm,
    arg: &SupTerm,
) -> SupFormula {
    match formula {
        Atom(pred_name, pred_args) => Atom(
            pred_name.to_string(),
            pred_args
                .iter()
                .map(|pred_arg| substitute_term(pred_arg, target, arg))
                .collect(),
        ),
        Equality(l, r) => Equality(
            substitute_term(l, target, arg),
            substitute_term(r, target, arg),
        ),
        Not(sub) => Not(Box::new(substitute_formula(sub, target, arg))),
        Clause(sub_formulas) => Clause(
            sub_formulas
                .iter()
                .map(|lit| substitute_formula(lit, target, arg))
                .collect(),
        ),
        ForAll(var_name, var_type, body) => ForAll(
            var_name.to_string(),
            Box::new(substitute_formula(var_type, target, arg)),
            Box::new(substitute_formula(body, target, arg)),
        ),
    }
}

/// Returns a clone of the first subterm of `term` that can be unified with `target`.
/// Terms&types are read left2right and binders are checked before bodies
pub fn find_unifiable_term(
    term: &SupTerm,
    target: &SupTerm,
) -> Option<SupTerm> {
    // TODO: support actual unification
    if Sup::base_term_equality(term, target).is_ok() {
        return Some(term.clone());
    }
    match term {
        Application(_, fun_args) => {
            for arg in fun_args {
                let rec_result = find_unifiable_term(arg, target);
                if !rec_result.is_none() {
                    return rec_result;
                }
            }
            return None;
        }
        _ => return None,
    }
}
/// Returns a clone of the first subterm of `formula` that can be unified with `target`.
/// Terms&types are read left2right and binders are checked before bodies
pub fn find_unifiable_formula(
    formula: &SupFormula,
    target: &SupTerm,
) -> Option<SupTerm> {
    match formula {
        Atom(_, pred_args) => {
            for arg in pred_args {
                let rec_result = find_unifiable_term(arg, target);
                if !rec_result.is_none() {
                    return rec_result;
                }
            }
            return None;
        }
        Equality(l, r) => {
            let left_result = find_unifiable_term(l, target);
            if left_result.is_some() {
                return left_result;
            } else {
                return find_unifiable_term(r, target);
            }
        }
        Not(sub) => find_unifiable_formula(sub, target),
        Clause(sub_formulas) => {
            for sub in sub_formulas {
                let rec_result = find_unifiable_formula(sub, target);
                if !rec_result.is_none() {
                    return rec_result;
                }
            }
            return None;
        }
        ForAll(_, var_type, body) => {
            let type_result = find_unifiable_formula(var_type, target);
            if type_result.is_some() {
                return type_result;
            } else {
                return find_unifiable_formula(body, target);
            }
        }
    }
}

/// Selection function to select a non-empty set of *literals* from a `clause`.
/// This function removes one literal from the input vector and returns it

pub type SelectionFunctionSignature = Box<
    dyn Fn(&mut Vec<SupFormula>) -> Result<Vec<SupFormula>, String>
        + Send
        + Sync,
>;

pub fn get_selection_fn(
    selection_fn: SelectionFunction,
) -> SelectionFunctionSignature {
    Box::new(move |clause: &mut Vec<SupFormula>| match selection_fn {
        Maximal() => Ok(drop_maximal_literals(clause)),
        All() => {
            let selected = clause.clone();
            *clause = vec![];
            Ok(selected)
        }
    })
}

#[cfg(test)]
mod tests {
    use crate::type_theory::sup::{
        sup::{
            SupFormula::{Atom, Clause, Equality, Not},
            SupTerm::{Application, Variable},
        },
        sup_utils::{
            drop_maximal_literals, is_tautology, kbo_terms, kbo_types, subsumes,
        },
    };
    use std::cmp::Ordering::{Equal, Greater, Less};

    #[test]
    fn test_tautology_detection() {
        let variable = Variable("x".to_string());
        let p = Atom("P".to_string(), vec![variable.clone()]);
        let q = Atom("Q".to_string(), vec![variable.clone()]);
        let taut = Equality(variable.clone(), variable.clone());

        assert!(
            is_tautology(&taut),
            "Tautology detection couldnt notice simple equality of identicals"
        );
        assert!(
            !is_tautology(&Clause(vec![])),
            "Tautology detection accepts the empty clause"
        );

        assert!(
            is_tautology(&Clause(vec![taut.clone()])),
            "Tautology detection couldnt notice clause containing a tautology"
        );

        assert!(
            is_tautology(&Clause(vec![
                p.clone(), q.clone(), Not(Box::new(p))
            ])),
            "Tautology detection couldnt notice clause with contradicting literals"
        );
    }

    #[test]
    // TODO add check for unification
    fn test_subsumption() {
        let variable = Variable("x".to_string());
        let p = Atom("P".to_string(), vec![variable.clone()]);
        let q = Atom("Q".to_string(), vec![variable.clone()]);

        assert!(
            subsumes(&Clause(vec![]), &Clause(vec![p.clone()])),
            "subsumption check doesnt work with emtpy clause"
        );

        assert!(
            subsumes(&Clause(vec![p.clone()]), &Clause(vec![p.clone()])),
            "subsumption check doesnt work with identical clauses"
        );

        assert!(
            subsumes(&Clause(vec![p.clone()]), &Clause(vec![q.clone(), p.clone()])),
            "subsumption check doesnt work with emtpy clause that extend the first one"
        );
    }

    #[test]
    fn test_kbo_term() {
        let anon = Variable("_".to_string());
        let arg = Variable("arg".to_string());

        assert_eq!(
            kbo_terms(&anon, &anon),
            Equal,
            "Identical terms arent equal by KB ordering"
        );

        assert_eq!(
            kbo_terms(&anon, &Application("f".to_string(), vec![arg.clone()])),
            Less,
            "simple variable isnt strictly less than function application"
        );
        assert_eq!(
            kbo_terms(&Application("f".to_string(), vec![arg.clone()]), &anon),
            Greater,
            "simple variable isnt strictly less than function application"
        );
    }

    #[test]
    fn test_kbo_types() {
        let n = Variable("n".to_string());
        let p = Atom("P".to_string(), vec![n.clone()]);
        let q = Atom("Q".to_string(), vec![n.clone()]);
        let r = Atom("R".to_string(), vec![n.clone()]);
        let short = Clause(vec![p.clone()]);
        let long = Clause(vec![p.clone(), q.clone(), r.clone()]);

        assert_eq!(
            kbo_types(&short, &long),
            Less,
            "Clause with less literals isnt strictly less than one with more"
        );
        assert_eq!(
            kbo_types(&long, &short),
            Greater,
            "Clause with less literals isnt strictly less than one with more"
        );
        assert_eq!(
            kbo_types(&p, &q),
            Equal,
            "Clause with less literals isnt strictly less than one with more"
        );
    }

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
