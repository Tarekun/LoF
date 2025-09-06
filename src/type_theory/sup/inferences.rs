use crate::misc::simple_map;
use crate::type_theory::interface::{Automatic, TypeTheory};
use crate::type_theory::sup::sup::{
    Sup,
    SupFormula::{self, Atom, Clause, Equality, ForAll, Not},
    SupTerm::{self, Application, Variable},
};
use crate::type_theory::sup::sup_utils::subsumes;
use std::cmp::{max_by, min_by};

fn substitute_term_in_term(
    base: &SupTerm,
    target: &SupTerm,
    body: &SupTerm,
) -> SupTerm {
    match base {
        // TODO if this is for demodulation this should check for alpha equivalence
        // and return body with the mgu applied
        _ if Sup::base_term_equality(base, target).is_ok() => {
            return body.to_owned();
        }
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

        // TODO also support mgu
        // if Sup::compare_types(D, C).is_ge() {
        substitute_term_in_type(C, max, min)
        // } else {
        //     C.to_owned()
        // }
    } else {
        C.to_owned()
    }
}

#[allow(non_snake_case)]
/// Applies subsumption resolution inference simplifying the first argument `C`
pub fn subsumption_resolution_first(
    C: &SupFormula,
    D: &SupFormula,
) -> SupFormula {
    println!("simplifiable: {:?}", C);
    println!("other clause: {:?}", D);
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

    println!("examined from simplifiable {:?}", c_first);
    println!("examined from other one {:?}", d_first);

    match (c_first, d_first) {
        (Not(inner), Atom(_, _)) => {
            let mut d_new = d_rest.to_vec();
            d_new.push((*d_first).clone());
            let mut c_new = c_rest.to_vec();
            c_new.push((**inner).clone());

            println!("subsumption check between {:?} <: {:?}", d_new, c_new);
            if subsumes(&Clause(d_new), &Clause(c_new)) {
                Clause(c_rest.to_vec())
            } else {
                C.to_owned()
            }
        }
        (Atom(_, _), Not(inner)) => {
            let mut d_new = d_rest.to_vec();
            d_new.push((**inner).clone());
            let mut c_new = c_rest.to_vec();
            c_new.push((*c_first).clone());

            if subsumes(&Clause(d_new), &Clause(c_new)) {
                Clause(c_rest.to_vec())
            } else {
                C.to_owned()
            }
        }
        _ => C.to_owned(),
    }
}

#[cfg(test)]
mod unit_tests {
    use crate::type_theory::sup::inferences::{
        demodulate_first, subsumption_resolution_first,
    };
    use crate::type_theory::sup::sup::SupFormula::{
        Atom, Clause, Equality, Not,
    };
    use crate::type_theory::sup::sup::SupTerm::{Application, Variable};

    #[test]
    fn test_demodulation() {
        let left = Application(
            "f".to_string(),
            vec![
                Application("g".to_string(), vec![Variable("x".to_string())]),
                Application("h".to_string(), vec![Variable("z".to_string())]),
            ],
        );
        let right = Application(
            "f".to_string(),
            vec![Variable("x".to_string()), Variable("z".to_string())],
        );
        let clause = Clause(vec![Atom("P".to_string(), vec![left.clone()])]);

        assert_eq!(
            demodulate_first(&clause, &Equality(left.clone(), right.clone())),
            Clause(vec![Atom("P".to_string(), vec![right.clone()])]),
            "Demodulation didnt simplify function argument using the provided equality"
        );
    }

    #[test]
    fn test_subsumption() {
        let p = Atom("P".to_string(), vec![Variable("x".to_string())]);
        let extras =
            vec![Atom("R".to_string(), vec![Variable("z".to_string())])];

        // this clause is ¬ P x ∨ R z
        let mut second_clause = extras.clone();
        second_clause.insert(0, Not(Box::new(p.clone())));
        assert_eq!(
            subsumption_resolution_first(
                &Clause(second_clause),     // ¬ P x ∨ R z
                &Clause(vec![p.clone()]),   // P x
            ),
            Clause(extras.clone()),
            "Subsumption couldnt resolve clause containing a contradiction with with provided clause"
        );
    }
}
