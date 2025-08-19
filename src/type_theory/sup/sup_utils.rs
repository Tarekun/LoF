use super::sup::{
    Sup,
    SupFormula::{self, Atom, Clause, Equality, ForAll, Not},
    SupTerm::{self, Application, Variable},
};
use crate::{
    misc::simple_map,
    type_theory::interface::{Automatic, TypeTheory},
};
use std::cmp::{
    max_by, min_by,
    Ordering::{self, Equal},
};

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
        (Variable(name1), Variable(name2)) => name1.cmp(name2),
        (Variable(_), Application(_, _)) => Ordering::Less,
        (Application(_, _), Variable(_)) => Ordering::Greater,
        (Application(f1, args1), Application(f2, args2)) => {
            match args1.len().cmp(&args2.len()) {
                Ordering::Equal => {
                    for (argl, argr) in args1.iter().zip(args2.iter()) {
                        match kbo_terms(argl, argr) {
                            Ordering::Equal => continue,
                            non_eq => return non_eq,
                        }
                    }
                    f1.cmp(f2)
                }
                non_eq => non_eq,
            }
        }
    }
}
pub fn kbo_types(φ1: &SupFormula, φ2: &SupFormula) -> Ordering {
    match (φ1, φ2) {
        (Atom(p1, args1), Atom(p2, args2)) => {
            match args1.len().cmp(&args2.len()) {
                Equal => {
                    for (a1, a2) in args1.iter().zip(args2.iter()) {
                        match kbo_terms(a1, a2) {
                            Equal => continue,
                            non_eq => return non_eq,
                        }
                    }
                    p1.cmp(&p2)
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
        (ForAll(v1, _, body1), ForAll(v2, _, body2)) => {
            match kbo_types(body1, body2) {
                Equal => v1.cmp(v2),
                non_eq => non_eq,
            }
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

fn substitute_term_in_term(
    base: &SupTerm,
    target: &SupTerm,
    body: &SupTerm,
) -> SupTerm {
    // TODO if this is for demodulation this should check for alpha equivalence
    // and return body with the mgu applied
    if Sup::base_term_equality(base, target).is_ok() {
        return body.to_owned();
    }
    match base {
        Application(fun_name, args) => Application(
            fun_name.to_string(),
            simple_map(args.to_owned(), |arg| {
                substitute_term_in_term(&arg, target, body)
            }),
        ),
        Variable(_) => base.to_owned(),
    }
}
fn substitute_term_in_type(
    base: &SupFormula,
    target: &SupTerm,
    body: &SupTerm,
) -> SupFormula {
    match base {
        Atom(name, args) => Atom(
            name.to_string(),
            simple_map(args.to_owned(), |arg| {
                substitute_term_in_term(&arg, target, body)
            }),
        ),
        Equality(l, r) => Equality(
            substitute_term_in_term(&l, target, body),
            substitute_term_in_term(&r, target, body),
        ),
        Not(phi) => Not(Box::new(substitute_term_in_type(phi, target, body))),
        ForAll(var_name, var_type, predicate) => ForAll(
            var_name.to_string(),
            Box::new(substitute_term_in_type(var_type, target, body)),
            Box::new(substitute_term_in_type(predicate, target, body)),
        ),
        Clause(lits) => Clause(simple_map(lits.to_owned(), |lit| {
            substitute_term_in_type(&lit, target, body)
        })),
    }
}

#[allow(non_snake_case)]
/// Applies a demodulation simplification rule to C,D, special case of superposition
/// inference where one of the clauses is a single equality and we rewrite by the smaller term.
/// only the first argument `C` will be simplified
pub fn demodulate_first(C: &SupFormula, D: &SupFormula) -> SupFormula {
    if let Equality(l, r) = D {
        let min = min_by(l, r, |l, r| Sup::compare_terms(l, r));
        let max = max_by(l, r, |l, r| Sup::compare_terms(l, r));

        let C = substitute_term_in_type(C, max, min);
        C
    } else {
        C.to_owned()
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
/// Applies subsumption resolution inference simplifying the first argument `C`
pub fn subsumption_resolution_first(
    C: &SupFormula,
    D: &SupFormula,
) -> SupFormula {
    let Clause(c_lits) = C else {
        return D.to_owned();
    };
    let Clause(d_lits) = D else {
        return D.to_owned();
    };
    let [c_first, c_rest @ ..] = c_lits.as_slice() else {
        return D.to_owned();
    };
    let [d_first, d_rest @ ..] = d_lits.as_slice() else {
        return D.to_owned();
    };

    match (c_first, d_first) {
        (Not(inner), Atom(_, _)) => {
            let mut d_new = d_rest.to_vec();
            d_new.push((*d_first).clone());
            let mut c_new = c_rest.to_vec();
            c_new.push((**inner).clone());

            if subsumes(&Clause(d_new), &Clause(c_new)) {
                Clause(d_rest.to_vec())
            } else {
                D.to_owned()
            }
        }
        (Atom(_, _), Not(inner)) => {
            let mut d_new = d_rest.to_vec();
            d_new.push((**inner).clone());
            let mut c_new = c_rest.to_vec();
            c_new.push((*c_first).clone());

            if subsumes(&Clause(d_new), &Clause(c_new)) {
                Clause(d_rest.to_vec())
            } else {
                D.to_owned()
            }
        }
        _ => D.to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use crate::type_theory::sup::{
        sup::{
            SupFormula::{Atom, Clause, Equality, Not},
            SupTerm::{Application, Variable},
        },
        sup_utils::{is_tautology, kbo_terms, kbo_types, subsumes},
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
    }
}
