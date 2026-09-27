use crate::error::LofError;
use crate::type_theory::{
    commons::unification::Substitution,
    grammars::cnf::{
        CnfFormula::{self, Atom, Clause, Equality, ForAll, Not},
        CnfTerm::{self, Application, Variable},
    },
    sup::unification::terms_unify,
};
use std::cmp::Ordering::{self, Equal, Greater, Less};

/// Returns the ordered vector of formal argument types of nested universal quantification
pub fn get_arg_types(forall: &CnfFormula) -> Vec<CnfFormula> {
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
pub fn get_forall_innermost(forall: &CnfFormula) -> CnfFormula {
    match forall {
        ForAll(_, _, body) => get_forall_innermost(&body),
        _ => forall.to_owned(),
    }
}

/// Implements standard Knuth-Bendix ordering of terms. Ordering ties are not
/// broken using the internal names, so ex. `Variable`s are all isomorphic
pub fn kbo_terms(term1: &CnfTerm, term2: &CnfTerm) -> Ordering {
    fn weight(term: &CnfTerm) -> i32 {
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
pub fn kbo_types(φ1: &CnfFormula, φ2: &CnfFormula) -> Ordering {
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
            // TODO: revise this
            kbo_types(body1, body2)
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

/// Returns a clone of the first subterm of `term` that can be unified with `target`.
/// Terms&types are read left2right and binders are checked before bodies
pub fn find_unifiable_term(
    term: &CnfTerm,
    target: &CnfTerm,
) -> Option<(CnfTerm, Substitution<CnfTerm>)> {
    if let Ok(mgu) = terms_unify(term, target) {
        return Some((term.clone(), mgu));
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
    formula: &CnfFormula,
    target: &CnfTerm,
) -> Option<(CnfTerm, Substitution<CnfTerm>)> {
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

/// Reserved predicate name for answer literals
const ANSWER_PREDICATE: &str = "$answer";

/// Collects unbound variable names of `formula` in order of occurrence, without duplicates
fn collect_vars(formula: &CnfFormula) -> Vec<String> {
    fn collect_term_vars(term: &CnfTerm, vars: &mut Vec<String>) {
        match term {
            Variable(name) if !vars.contains(name) => vars.push(name.clone()),
            Variable(_) => {}
            Application(_, args) => {
                args.iter().for_each(|a| collect_term_vars(a, vars))
            }
        }
    }

    fn solver(formula: &CnfFormula, vars: &mut Vec<String>) {
        match formula {
            Atom(_, args) => {
                args.iter().for_each(|a| collect_term_vars(a, vars))
            }
            Equality(l, r) => {
                collect_term_vars(l, vars);
                collect_term_vars(r, vars);
            }
            Not(inner) => solver(inner, vars),
            Clause(lits) => lits.iter().for_each(|l| solver(l, vars)),
            ForAll(_, ty, body) => {
                solver(ty, vars);
                solver(body, vars);
            }
        }
    }

    let mut vars = vec![];
    solver(formula, &mut vars);
    vars
}

/// Returns `clause` extended with an answer literal tracking all of its free variables
pub fn with_answer_literal(clause: &CnfFormula) -> CnfFormula {
    let vars = collect_vars(clause);
    if vars.is_empty() {
        return clause.to_owned();
    }

    let mut literals = clause.unpack_literals();
    literals.push(Atom(
        ANSWER_PREDICATE.to_string(),
        vars.into_iter()
            // TODO constructing $answer($v(v)) is hack to get around the fact that
            // standardize_apart would rename variables to v_idx but doesnt do that
            // on function names. `saturate` should be reworked to have the original
            // variable list so we can avoid creating this odd answer literal
            .map(|v| Application(format!("${}", v), vec![Variable(v)]))
            .collect(),
    ));
    Clause(literals)
}

pub fn is_answer_literal(literal: &CnfFormula) -> bool {
    matches!(literal, Atom(pred, _) if pred == ANSWER_PREDICATE)
}

/// Returns the answer substitution tracked by `clause`, assumed to be a refutation made
/// only of answer literals. Different answer literals `$answer(a) ∨ $answer(b)`
/// only prove a disjunction of answers and fail
pub fn extract_answer(
    clause: &CnfFormula,
) -> Result<Substitution<CnfTerm>, LofError> {
    let answers = clause.unpack_literals();
    let Some(Atom(_, args)) = answers.first() else {
        return Ok(Substitution::empty());
    };
    if answers.iter().any(|answer| *answer != answers[0]) {
        // TODO rethink this and check it makes sense
        return Err(LofError::custom(format!(
            "Found a refutation, but only for the disjunctive answer {:?}",
            clause
        )));
    }

    Ok(Substitution::from(args.iter().filter_map(
        |arg| match arg {
            Application(name, inner) if inner.len() == 1 => {
                Some((name.strip_prefix('$')?.to_string(), inner[0].clone()))
            }
            _ => None,
        },
    )))
}

#[cfg(test)]
mod tests {
    use crate::type_theory::commons::unification::Substitution;
    use crate::type_theory::grammars::cnf::{
        CnfFormula::{Atom, Clause, Equality, Not},
        CnfTerm::{self, Application, Variable},
    };
    use crate::type_theory::sup::sup_utils::{
        extract_answer, kbo_terms, kbo_types, with_answer_literal,
    };
    use std::cmp::Ordering::{Equal, Greater, Less};

    #[test]
    fn test_answer_literal() {
        let r = Variable("R".to_string());
        let a = Application("a".to_string(), vec![]);
        let b = Application("b".to_string(), vec![]);
        let goal =
            Not(Box::new(Atom("P".to_string(), vec![r.clone(), r.clone()])));

        let tracked = with_answer_literal(&goal).standardize_apart();
        let Clause(lits) = &tracked else {
            panic!("expected a clause")
        };
        let answer = lits.last().unwrap().clone();
        let Atom(_, args) = &answer else {
            panic!("expected an atom")
        };
        let Application(_, inner) = &args[0] else {
            panic!("expected wrapper")
        };
        assert_eq!(
            args.len(),
            1,
            "Answer literal doesnt track each variable once"
        );
        assert_ne!(
            inner[0], r,
            "Answer literal variable wasnt renamed with its clause"
        );
        assert_eq!(
            extract_answer(&Clause(vec![answer.clone(), answer.clone()]))
                .unwrap()
                .resolvent("R"),
            Some(&inner[0]),
            "Answer isnt keyed by the original variable name after renaming"
        );

        assert_eq!(
            extract_answer(&Clause(vec![])),
            Ok(Substitution::empty()),
            "Empty clause doesnt give an empty answer"
        );

        let answer_a =
            with_answer_literal(&Atom("P".to_string(), vec![r.clone()]));
        let Clause(lits) = answer_a else {
            panic!("expected a clause")
        };
        let instance = |t: &CnfTerm| lits[1].substitute_formula(&r, t);
        assert!(
            extract_answer(&Clause(vec![instance(&a), instance(&b)])).is_err(),
            "Disjunctive answer is accepted as a definite answer"
        );
        assert_eq!(
            extract_answer(&instance(&a)).unwrap().resolvent("R"),
            Some(&a),
            "Unit answer literal isnt extracted"
        );
        assert_eq!(
            with_answer_literal(&Atom("P".to_string(), vec![a.clone()])),
            Atom("P".to_string(), vec![a.clone()]),
            "Ground clause got an answer literal"
        );
    }

    #[test]
    fn test_tautology_detection() {
        let variable = Variable("x".to_string());
        let p = Atom("P".to_string(), vec![variable.clone()]);
        let q = Atom("Q".to_string(), vec![variable.clone()]);
        let taut = Equality(variable.clone(), variable.clone());

        assert!(
            taut.is_tautology(),
            "Tautology detection couldnt notice simple equality of identicals"
        );
        assert!(
            !Clause(vec![]).is_tautology(),
            "Tautology detection accepts the empty clause"
        );

        assert!(
            Clause(vec![taut.clone()]).is_tautology(),
            "Tautology detection couldnt notice clause containing a tautology"
        );

        assert!(
            Clause(vec![p.clone(), q.clone(), Not(Box::new(p))]).is_tautology(),
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
            Clause(vec![]).subsumes(&Clause(vec![p.clone()])),
            "subsumption check doesnt work with emtpy clause"
        );

        assert!(
            Clause(vec![p.clone()]).subsumes(&Clause(vec![p.clone()])),
            "subsumption check doesnt work with identical clauses"
        );

        assert!(
            Clause(vec![p.clone()])
                .subsumes(&Clause(vec![q.clone(), p.clone()])),
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
}
