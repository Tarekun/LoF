use rand::rand_core::le;

use crate::type_theory::interface::{Automatic, TypeTheory};
use crate::type_theory::sup::sup_utils::{subsumes, unpack_literals};
use crate::{
    misc::simple_map,
    type_theory::sup::sup::{
        Sup,
        SupFormula::{self, Atom, Clause, Equality, ForAll, Not},
        SupTerm::{self, Application, Variable},
    },
};
use std::cmp::{max_by, min_by};

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

//########################### SIMPLIFICATION INFERENCES
#[allow(non_snake_case)]
/// Applies a demodulation simplification rule to C,D, special case of superposition
/// inference where one of the clauses is a single equality and we rewrite by the smaller term.
/// only the first argument `C` will be simplified
pub fn demodulate_first(C: &SupFormula, D: &SupFormula) -> SupFormula {
    if let Equality(l, r) = D {
        let min = min_by(l, r, |l, r| Sup::compare_terms(l, r));
        let max = max_by(l, r, |l, r| Sup::compare_terms(l, r));

        // TODO also support mgu
        substitute_term_in_type(C, max, min)
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
    let Ok(c_lits) = unpack_literals(C) else {
        return C.to_owned();
    };
    let Ok(d_lits) = unpack_literals(D) else {
        return C.to_owned();
    };
    let [c_first, c_rest @ ..] = c_lits.as_slice() else {
        return C.to_owned();
    };
    let [d_first, d_rest @ ..] = d_lits.as_slice() else {
        return C.to_owned();
    };

    match (c_first, d_first) {
        (Not(inner), Atom(_, _)) => {
            let mut d_new = d_rest.to_vec();
            d_new.push((*d_first).clone());
            let mut c_new = c_rest.to_vec();
            c_new.push((**inner).clone());

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
//########################### SIMPLIFICATION INFERENCES

//########################### SUP INFERENCES
// pub fn resolution(
//     C: &SupFormula,
//     D: &SupFormula,
// ) -> Result<SupFormula, String> {
//     let mut c_literals = unpack_literals(C)?.clone();
//     let mut d_literals = unpack_literals(D)?.clone();
//     let selected = Sup::select(&mut c_literals)?;

//     match &selected {
//         Atom(_, _) => {
//             for i in 0..d_literals.len() {
//                 if let Not(inner) = &d_literals[i] {
//                     // TODO support mcu
//                     if Sup::base_type_equality(&selected, inner).is_ok() {
//                         d_literals.remove(i);
//                         c_literals.extend(d_literals);
//                         return Ok(Clause(c_literals));
//                     }
//                 }
//             }
//         }
//         Not(inner) => {
//             for i in 0..d_literals.len() {
//                 if let Atom(_, _) = d_literals[i] {
//                     // TODO support mcu
//                     if Sup::base_type_equality(inner, &d_literals[i]).is_ok() {
//                         d_literals.remove(i);
//                         c_literals.extend(d_literals);
//                         return Ok(Clause(c_literals));
//                     }
//                 }
//             }
//         }
//         _ => {}
//     }

//     Err(format!(
//         "Resolution cannot be applied to clauses {:?}, {:?} with picked (from first) literal {:?}",
//         C, D, selected
//     ))
// }

// pub fn factoring(C: &SupFormula) -> Result<SupFormula, String> {
//     let lits = unpack_literals(C)?;
//     let mut literals = lits.clone();
//     let selected = Sup::select(&mut literals)?;

//     for i in 0..literals.len() {
//         // TODO support mgu check here
//         if Sup::base_type_equality(&literals[i], &selected).is_ok() {
//             // TODO apply mgu to literals
//             return Ok(Clause(literals));
//         }
//     }

//     Err(format!(
//         "Factoring cannot be applied to clause {:?} with picked literal {:?}",
//         C, selected
//     ))
// }

// pub fn eq_resolution(C: &SupFormula) -> Result<SupFormula, String> {
//     let mut lits = unpack_literals(C)?.clone();
//     let selected = Sup::select(&mut lits)?;

//     match &selected {
//         Not(boxed) => {
//             if let Equality(l, r) = &**boxed {
//                 // TODO support mgu check here
//                 if Sup::base_term_equality(l, r).is_ok() {
//                     return Ok(Clause(lits));
//                 }
//             }
//         }
//         _ => {}
//     }

//     Err(format!(
//         "Equality resolution cannot be applied to clause {:?} with picked literal {:?}",
//         C, selected
//     ))
// }

// pub fn eq_factoring(C: &SupFormula) -> Result<SupFormula, String> {
//     let mut literals: Vec<SupFormula> = unpack_literals(C)?.clone();
//     let selected = Sup::select(&mut literals)?[0].clone();

//     if let Equality(s, t) = &selected {
//         let min = min_by(s, t, |s, t| Sup::compare_terms(s, t));
//         let max = max_by(s, t, |s, t| Sup::compare_terms(s, t));

//         for lit in &literals {
//             if let Equality(l, r) = lit {
//                 if Sup::base_term_equality(max, l).is_ok() {
//                     let mut new_literals = literals.clone();
//                     new_literals.push(selected.clone());
//                     new_literals
//                         .push(Not(Box::new(Equality(min.clone(), r.clone()))));
//                     return Ok(Clause(new_literals));
//                 }
//             }
//         }
//     }

//     Err(format!(
//         "Equality resolution cannot be applied to clause {:?} with picked literal {:?}",
//         C, selected
//     ))
// }
// //########################### SUP INFERENCES

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
