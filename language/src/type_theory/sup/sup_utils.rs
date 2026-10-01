use crate::error::LofError;
use crate::type_theory::{
    commons::unification::Substitution,
    grammars::{
        cnf::{
            CnfFormula::{self, Atom, Clause, Equality, ForAll, Not},
            CnfTerm::{self, Application, Variable},
        },
        traits::Unification,
    },
};
use std::cmp::Ordering::{self, Equal, Greater, Less};
use std::collections::HashMap;

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
/// broken using the internal names, so ex. `Variable`s are all isomorphic.
/// Terms that can't be ordered return `Equal`
pub fn kbo_terms(term1: &CnfTerm, term2: &CnfTerm) -> Ordering {
    /// Every symbol and variable weighs 1, so a term weighs its size and is
    /// always heavier than its proper subterms
    fn weight(term: &CnfTerm) -> usize {
        match term {
            Variable(_) => 1,
            Application(_, args) => 1 + args.iter().map(weight).sum::<usize>(),
        }
    }
    fn count_vars(term: &CnfTerm, counts: &mut HashMap<String, usize>) {
        match term {
            Variable(var) => *counts.entry(var.clone()).or_default() += 1,
            Application(_, args) => {
                args.iter().for_each(|arg| count_vars(arg, counts))
            }
        }
    }
    /// Variable condition: a term can only be greater than another if each
    /// variable occurs in it at least as many times. Otherwise substituting a
    /// large enough term for a variable could reverse the ordering, eg
    /// f(X, a, a) is heavier than g(X, X) but f(h(h(a)), a, a) isnt heavier
    /// than g(h(h(a)), h(h(a)))
    fn dominates(
        counts: &HashMap<String, usize>,
        other: &HashMap<String, usize>,
    ) -> bool {
        other
            .iter()
            .all(|(var, n)| counts.get(var).is_some_and(|m| m >= n))
    }

    let (mut vars1, mut vars2) = (HashMap::new(), HashMap::new());
    count_vars(term1, &mut vars1);
    count_vars(term2, &mut vars2);

    let ordering = match weight(term1).cmp(&weight(term2)) {
        Equal => match (term1, term2) {
            // in case terms have the same weight
            (Variable(_), Variable(_)) => Equal,
            (Variable(_), Application(_, _)) => Less,
            (Application(_, _), Variable(_)) => Greater,
            (Application(_, args1), Application(_, args2)) => {
                match args1.len().cmp(&args2.len()) {
                    Equal => args1
                        .iter()
                        .zip(args2)
                        .map(|(argl, argr)| kbo_terms(argl, argr))
                        .find(|ordering| *ordering != Equal)
                        .unwrap_or(Equal),
                    non_eq => non_eq,
                }
            }
        },
        non_eq => non_eq,
    };
    match ordering {
        Greater if dominates(&vars1, &vars2) => Greater,
        Less if dominates(&vars2, &vars1) => Less,
        _ => Equal,
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

        // order formulas by constructor kind if they are different. negative
        // literals are greater than positive ones, as in the SUP literal
        // ordering ¬(s = t) is the multiset {s, s, t, t} while s = t is {s, t}
        (Atom(_, _), _) => Ordering::Less,
        (_, Atom(_, _)) => Ordering::Greater,
        (Equality(_, _), _) => Ordering::Less,
        (_, Equality(_, _)) => Ordering::Greater,
        (Not(_), _) => Ordering::Less,
        (_, Not(_)) => Ordering::Greater,
        (Clause(_), _) => Ordering::Less,
        (_, Clause(_)) => Ordering::Greater,
    }
}

/// One way matching: returns the substitution σ of the variables of `pattern`
/// such that `pattern`σ = `term`, if any. The variables of `term` are left
/// untouched, as if they were constants
pub fn match_term(
    pattern: &CnfTerm,
    term: &CnfTerm,
) -> Option<Substitution<CnfTerm>> {
    fn solver(
        pattern: &CnfTerm,
        term: &CnfTerm,
        bindings: &mut HashMap<String, CnfTerm>,
    ) -> bool {
        match (pattern, term) {
            (Variable(var), _) => match bindings.get(var) {
                Some(bound) => bound == term,
                None => {
                    bindings.insert(var.clone(), term.clone());
                    true
                }
            },
            (Application(f, f_args), Application(g, g_args)) => {
                f == g
                    && f_args.len() == g_args.len()
                    && f_args
                        .iter()
                        .zip(g_args)
                        .all(|(p, t)| solver(p, t, bindings))
            }
            _ => false,
        }
    }

    let mut bindings = HashMap::new();
    solver(pattern, term, &mut bindings).then(|| Substitution::from(bindings))
}

/// Returns a clone of the first subterm of `term` that can be unified with `target`.
/// Terms&types are read left2right and binders are checked before bodies
pub fn find_unifiable_term(
    term: &CnfTerm,
    target: &CnfTerm,
) -> Option<(CnfTerm, Substitution<CnfTerm>)> {
    if let Ok(mgu) = term.unifies(target) {
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
    use crate::type_theory::grammars::traits::Unification;
    use crate::type_theory::sup::freedom::drop_maximal_literals;
    use crate::type_theory::sup::sup_utils::{
        extract_answer, kbo_terms, kbo_types, match_term, with_answer_literal,
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
    fn test_match_term() {
        let var = |name: &str| Variable(name.to_string());
        let f =
            |l: CnfTerm, r: CnfTerm| Application("f".to_string(), vec![l, r]);
        let a = Application("a".to_string(), vec![]);

        let σ = match_term(&f(var("X"), var("X")), &f(a.clone(), a.clone()))
            .expect("A pattern doesnt match its instance");
        assert_eq!(σ.get("X"), Some(&a));
        assert!(
            match_term(&f(var("X"), var("X")), &f(a.clone(), var("Y")))
                .is_none(),
            "A pattern matches binding one variable to two different terms"
        );
        assert!(
            match_term(&f(a.clone(), var("X")), &f(var("Y"), a.clone()))
                .is_none(),
            "Matching binds variables of the matched term"
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
            kbo_terms(&anon, &Application("f".to_string(), vec![anon.clone()])),
            Less,
            "simple variable isnt strictly less than function application"
        );
        assert_eq!(
            kbo_terms(&Application("f".to_string(), vec![anon.clone()]), &anon),
            Greater,
            "simple variable isnt strictly less than function application"
        );
        assert_eq!(
            kbo_terms(&anon, &Application("f".to_string(), vec![arg.clone()])),
            Equal,
            "variable is ordered against a term it doesnt occur in"
        );
    }

    #[test]
    fn test_kbo_term_stable_under_substitution() {
        let x = Variable("X".to_string());
        let a = Application("a".to_string(), vec![]);
        let h = |t: CnfTerm| Application("h".to_string(), vec![t]);
        let f = |args: Vec<CnfTerm>| Application("f".to_string(), args);
        let g = |args: Vec<CnfTerm>| Application("g".to_string(), args);
        let σ = Substitution::from([("X".to_string(), h(h(a.clone())))]);

        // f(X, a, a) is heavier than g(X, X), but X occurs more in g
        let left = f(vec![x.clone(), a.clone(), a.clone()]);
        let right = g(vec![x.clone(), x.clone()]);
        assert_eq!(
            kbo_terms(
                &left.apply_substitution(&σ),
                &right.apply_substitution(&σ)
            ),
            Less,
            "f(h(h(a)), a, a) isnt less than g(h(h(a)), h(h(a)))"
        );
        assert_eq!(
            kbo_terms(&left, &right),
            Equal,
            "terms are ordered although an instance reverses their ordering"
        );
        assert_eq!(
            kbo_terms(&right, &left),
            Equal,
            "terms are ordered although an instance reverses their ordering"
        );

        // f(X, X) is heavier than g(X) and stays so in every instance
        assert_eq!(
            kbo_terms(&f(vec![x.clone(), x.clone()]), &g(vec![x.clone()])),
            Greater,
            "terms satisfying the variable condition arent ordered by weight"
        );
    }

    #[test]
    fn test_kbo_term_weights_whole_terms() {
        let zero = Application("0".to_string(), vec![]);
        let s = |t: CnfTerm| Application("s".to_string(), vec![t]);
        let add =
            |l: CnfTerm, r: CnfTerm| Application("+".to_string(), vec![l, r]);
        let small =
            add(s(Variable("n".to_string())), Variable("m".to_string()));
        let big = add(zero.clone(), small.clone());

        // with weights counting only direct arguments both weigh 3, and the
        // tie is broken by s(n) > 0, letting demodulation by 0 + x = x
        // rewrite +(s(n), m) to the larger +(0, +(s(n), m)) forever
        assert_eq!(
            kbo_terms(&small, &big),
            Less,
            "A term isnt less than a term containing it"
        );
        assert_eq!(
            kbo_terms(&big, &small),
            Greater,
            "A term isnt greater than its proper subterms"
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
    fn test_negative_literals_exceed_equalities() {
        let (x, y) = (Variable("X".to_string()), Variable("Y".to_string()));
        let f = |t: &CnfTerm| Application("f".to_string(), vec![t.clone()]);
        let equality = Equality(x.clone(), y.clone());
        let negated_equality = Not(Box::new(Equality(f(&x), f(&y))));
        let negated_atom =
            Not(Box::new(Atom("P".to_string(), vec![x.clone(), y.clone()])));

        assert_eq!(
            kbo_types(&negated_equality, &equality),
            Greater,
            "Negated equalities arent greater than equalities"
        );
        assert_eq!(
            kbo_types(&equality, &negated_atom),
            Less,
            "Equalities arent less than negated atoms"
        );

        // X = Y ∨ ¬P(X, Y) ∨ f(X) ≠ f(Y): selecting the non orientable X = Y
        // lets it superpose into every term
        let mut clause = vec![
            equality.clone(),
            negated_atom.clone(),
            negated_equality.clone(),
        ];
        let selected = drop_maximal_literals(&mut clause);
        assert!(
            !selected.contains(&equality),
            "Maximal literal selection picks a positive equality over negative literals"
        );
    }
}
