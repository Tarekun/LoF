use crate::type_theory::interface::{Automatic, TypeTheory};
use crate::type_theory::sup::sup_utils::{
    find_unifiable_formula, substitute_formula, subsumes, unpack_literals,
};
use crate::{
    misc::simple_map,
    type_theory::sup::sup::{
        Sup,
        SupFormula::{self, Atom, Clause, Equality, ForAll, Not},
        SupTerm::{self, Application, Variable},
    },
};
use std::cmp::{max_by, min_by, Ordering::Less};

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
#[allow(non_snake_case)]
pub fn resolution(
    C: &SupFormula,
    D: &SupFormula,
) -> Result<SupFormula, String> {
    let mut c_literals = unpack_literals(C)?.clone();
    let mut d_literals = unpack_literals(D)?.clone();
    let selected = Sup::select(&mut c_literals)?;

    for selected_atom in selected.iter() {
        match selected_atom {
            Atom(_, _) => {
                for i in 0..d_literals.len() {
                    if let Not(inner) = &d_literals[i] {
                        // TODO support mcu
                        if Sup::base_type_equality(&selected_atom, inner)
                            .is_ok()
                        {
                            d_literals.remove(i);
                            c_literals.extend(d_literals);
                            // TODO reinclude other selected atoms in lits
                            return Ok(Clause(c_literals));
                        }
                    }
                }
            }
            Not(inner) => {
                for i in 0..d_literals.len() {
                    if let Atom(_, _) = d_literals[i] {
                        // TODO support mcu
                        if Sup::base_type_equality(inner, &d_literals[i])
                            .is_ok()
                        {
                            d_literals.remove(i);
                            c_literals.extend(d_literals);
                            return Ok(Clause(c_literals));
                        }
                    }
                }
            }
            _ => {}
        }
    }

    Err(format!(
        "Resolution cannot be applied to clauses {:?}, {:?} with picked literals (from first) {:?}",
        C, D, selected
    ))
}

#[allow(non_snake_case)]
pub fn factoring(C: &SupFormula) -> Result<SupFormula, String> {
    let lits = unpack_literals(C)?;
    let mut literals = lits.clone();
    let selected = Sup::select(&mut literals)?;

    for i in 0..selected.len() {
        for j in i + 1..selected.len() {
            // TODO support mgu check here
            if Sup::base_type_equality(&selected[i], &selected[j]).is_ok() {
                // TODO apply mgu to literals
                // TODO reinclude other selected atoms in lits
                return Ok(Clause(literals));
            }
        }
    }

    Err(format!(
        "Factoring cannot be applied to clause {:?} with picked literal {:?}",
        C, selected
    ))
}

#[allow(non_snake_case)]
pub fn eq_resolution(C: &SupFormula) -> Result<SupFormula, String> {
    let mut lits = unpack_literals(C)?.clone();
    let selected = Sup::select(&mut lits)?;

    for selected_atom in selected.iter() {
        match selected_atom {
            Not(boxed) => {
                if let Equality(l, r) = &**boxed {
                    // TODO support mgu check here
                    if Sup::base_term_equality(l, r).is_ok() {
                        // TODO apply mgu to literals
                        // TODO reinclude other selected atoms in lits
                        return Ok(Clause(lits));
                    }
                }
            }
            _ => {}
        }
    }

    Err(format!(
        "Equality resolution cannot be applied to clause {:?} with picked literal {:?}",
        C, selected
    ))
}

/// macro that checks for equality factoring appliability. it assumes that the macro is called
/// from a clause in the form s=t ∨ s_prime=t_prime ∨ rest, where rest is a vector of atoms.
/// it works symmetrically on the first equality by computing max=max(s,t) and min=min(s,t);
/// then checks that min < max, max = s_prime, min < t_prime
macro_rules! eq_factoring_checks {
    ($s:expr, $t:expr, $s_prime:expr, $t_prime:expr, $rest:expr) => {{
        // TODO check s/t arent isomorphic
        let max = max_by($s, $t, |a, b| Sup::compare_terms(a, b));
        let min = min_by($s, $t, |a, b| Sup::compare_terms(a, b));

        // this bs of matching true is needed to not indent twice to check equality
        // and ordering. cuz to check ordering you need to match the variant and if let
        // definitions are "unstable" with multipled conditions
        // match works better then if. only in rust
        match (
            Sup::base_term_equality(max, $s_prime).is_ok(),
            Sup::compare_terms(min, $t_prime),
        ) {
            (true, Less) => {
                $rest.push(Equality($s.to_owned(), $t.to_owned()));
                $rest.push(Not(Box::new(Equality(
                    min.to_owned(),
                    $t.to_owned(),
                ))));
                return Ok(Clause($rest));
            }
            _ => {}
        }
    }};
}
#[allow(non_snake_case)]
pub fn eq_factoring(C: &SupFormula) -> Result<SupFormula, String> {
    let mut literals: Vec<SupFormula> = unpack_literals(C)?.clone();
    let selected = Sup::select(&mut literals)?;

    for i in 0..selected.len() {
        for j in i + 1..selected.len() {
            match (&selected[i], &selected[j]) {
                (Equality(l, r), Equality(s, t)) => {
                    eq_factoring_checks!(l, r, s, t, literals);
                    eq_factoring_checks!(l, r, t, s, literals);
                    // try swapped roles of equalities
                    eq_factoring_checks!(s, t, l, r, literals);
                    eq_factoring_checks!(s, t, r, l, literals);
                }
                _ => {}
            }
        }
    }

    Err(format!(
        "Equality resolution cannot be applied to clause {:?} with picked literal {:?}",
        C, selected
    ))
}

macro_rules! sup_inference {
    ($equality:expr, $other:expr) => {{
        match $equality {
            Equality(l, r) => {
                // TODO: check `other` isnt an equality. in that case find_unifiable should only look in 1 term
                let unifiable_term = find_unifiable_formula(&$other, &l);
                let (unifiable_term, target) = if unifiable_term.is_some() {
                    (unifiable_term, l)
                } else {
                    (find_unifiable_formula(&$other, &r), r)
                };

                if let Some(unifiable_term) = unifiable_term {
                    let other =
                        substitute_formula(&$other, &target, &unifiable_term);
                    Ok(other)
                } else {
                    Err("Non unifiable".to_string())
                }
            }
            _ => Err("Not equality".to_string()),
        }
    }};
}
#[allow(non_snake_case)]
pub fn superposition(
    C: &SupFormula,
    D: &SupFormula,
) -> Result<SupFormula, String> {
    let mut c_literals = unpack_literals(C)?.clone();
    let mut d_literals = unpack_literals(D)?.clone();
    let c_selected = Sup::select(&mut c_literals)?;
    let d_selected = Sup::select(&mut d_literals)?;

    for c_lit in &c_selected {
        for d_lit in &d_selected {
            let first_try = sup_inference!(c_lit, d_lit);
            if first_try.is_ok() {
                return first_try;
            } else {
                return sup_inference!(d_lit, c_lit);
            }
        }
    }

    Err(format!(
        "Superposition cannot be applied to clauses {:?}, {:?} with respective picked literals {:?}, {:?}",
        C, D, c_selected, d_selected
    ))
}
//########################### SUP INFERENCES

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
