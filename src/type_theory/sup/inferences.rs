use crate::type_theory::commons::unification::Substitution;
use crate::type_theory::interface::Automatic;
use crate::type_theory::sup::sup::SupTerm;
use crate::type_theory::sup::sup::{
    Sup,
    SupFormula::{self, Atom, Clause, Equality, Not},
};
use crate::type_theory::sup::sup_utils::{
    find_unifiable_formula, substitute_formula, subsumes, unpack_literals,
    SelectionFunctionSignature,
};
use crate::type_theory::sup::unification::{
    formula_apply_substitution, formulas_unify, term_apply_substitution,
    terms_unify,
};
use std::cmp::{max_by, min_by, Ordering::Less};

//########################### SIMPLIFICATION INFERENCES
#[allow(non_snake_case)]
/// Applies a demodulation simplification rule to C,D, special case of superposition
/// inference where one of the clauses is a single equality and we rewrite by the smaller term.
/// only the first argument `C` will be simplified
pub fn demodulate_first(C: &SupFormula, D: &SupFormula) -> SupFormula {
    if let Equality(l, r) = D {
        // TODO check l/r arent isomorphic
        let min = min_by(l, r, |l, r| Sup::compare_terms(l, r));
        let max = max_by(l, r, |l, r| Sup::compare_terms(l, r));

        // TODO also support mgu
        // TODO also return mgu
        // TODO verify this is correct. the paper references the requirement of (l=r) > C
        substitute_formula(C, max, min)
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
    // TODO also support/return mgu
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
macro_rules! resolution_inference {
    ($c_idx:expr, $d_idx:expr, $c_selected:expr, $d_selected:expr, $c_others:expr, $d_others:expr) => {{
        match $c_selected[$c_idx] {
            Atom(_, _) => {
                if let Not(inner) = &$d_selected[$d_idx] {
                    if let Ok(mgu) = formulas_unify(&$c_selected[$c_idx], inner)
                    {
                        let mut new_clause = vec![];
                        $c_selected.remove($c_idx);
                        new_clause.extend($c_selected);
                        new_clause.extend($c_others);
                        $d_selected.remove($d_idx);
                        new_clause.extend($d_selected);
                        new_clause.extend($d_others);
                        return Ok((
                            formula_apply_substitution(
                                &Clause(new_clause),
                                &mgu,
                            ),
                            mgu,
                        ));
                    }
                }
            }
            _ => {}
        }
    }};
}
#[allow(non_snake_case)]
pub fn resolution(
    C: &SupFormula,
    D: &SupFormula,
    selection_fn: &SelectionFunctionSignature,
) -> Result<(SupFormula, Substitution<SupTerm>), String> {
    let mut c_literals = unpack_literals(C)?;
    let mut d_literals = unpack_literals(D)?;
    let mut c_selected = selection_fn(&mut c_literals)?;
    let mut d_selected = selection_fn(&mut d_literals)?;

    for i in 0..c_selected.len() {
        for j in 0..d_selected.len() {
            resolution_inference!(
                i, j, c_selected, d_selected, c_literals, d_literals
            );
            resolution_inference!(
                j, i, d_selected, c_selected, d_literals, c_literals
            );
        }
    }

    Err(format!(
        "Resolution cannot be applied to clauses {:?}, {:?} with selected literals {:?}, {:?}",
        C, D, c_selected, d_selected
    ))
}

#[allow(non_snake_case)]
pub fn factoring(
    C: &SupFormula,
    selection_fn: &SelectionFunctionSignature,
) -> Result<(SupFormula, Substitution<SupTerm>), String> {
    let mut literals = unpack_literals(C)?;
    let mut selected = selection_fn(&mut literals)?;

    for i in 0..selected.len() {
        for j in i + 1..selected.len() {
            if let Ok(mgu) = formulas_unify(&selected[i], &selected[j]) {
                selected.remove(j);
                literals.extend(selected);
                return Ok((
                    formula_apply_substitution(&Clause(literals), &mgu),
                    mgu,
                ));
            }
        }
    }

    Err(format!(
        "Factoring cannot be applied to clause {:?} with picked literal {:?}",
        C, selected
    ))
}

#[allow(non_snake_case)]
pub fn eq_resolution(
    C: &SupFormula,
    selection_fn: &SelectionFunctionSignature,
) -> Result<(SupFormula, Substitution<SupTerm>), String> {
    let mut lits = unpack_literals(C)?;
    let mut selected = selection_fn(&mut lits)?;

    for i in 0..selected.len() {
        match &selected[i] {
            Not(boxed) => {
                if let Equality(l, r) = &**boxed {
                    if let Ok(mgu) = terms_unify(l, r) {
                        selected.remove(i);
                        lits.extend(selected);
                        return Ok((
                            formula_apply_substitution(&Clause(lits), &mgu),
                            mgu,
                        ));
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
    ($s:expr, $t:expr, $s_prime:expr, $t_prime:expr, $selected:expr, $unselected:expr, $i:expr, $j:expr) => {{
        // TODO check s/t arent isomorphic
        let max = max_by($s, $t, |a, b| Sup::compare_terms(a, b));
        let min = min_by($s, $t, |a, b| Sup::compare_terms(a, b));

        // this bs of matching true is needed to not indent twice to check equality
        // and ordering. cuz to check ordering you need to match the variant and if let
        // definitions are "unstable" with multipled conditions
        // match works better then if. only in rust
        match (
            terms_unify(max, $s_prime),
            Sup::compare_terms($t_prime, min),
        ) {
            (Ok(mgu), Less) => {
                $unselected.push(Equality($s.to_owned(), $t.to_owned()));
                $unselected.push(Not(Box::new(Equality(
                    min.to_owned(),
                    $t_prime.to_owned(),
                ))));
                $selected.remove($j);
                $selected.remove($i);

                $unselected.extend($selected);
                return Ok((formula_apply_substitution(&Clause($unselected), &mgu), mgu));
            }
            _ => {}
        }
    }};
}
#[allow(non_snake_case)]
pub fn eq_factoring(
    C: &SupFormula,
    selection_fn: &SelectionFunctionSignature,
) -> Result<(SupFormula, Substitution<SupTerm>), String> {
    let mut literals: Vec<SupFormula> = unpack_literals(C)?;
    let mut selected = selection_fn(&mut literals)?;

    for i in 0..selected.len() {
        for j in i + 1..selected.len() {
            match (&selected[i], &selected[j]) {
                (Equality(s, t), Equality(s_prime, t_prime)) => {
                    eq_factoring_checks!(
                        s, t, s_prime, t_prime, selected, literals, i, j
                    );
                    eq_factoring_checks!(
                        s, t, t_prime, s_prime, selected, literals, i, j
                    );
                    // try swapped roles of equalities
                    eq_factoring_checks!(
                        s_prime, t_prime, s, t, selected, literals, i, j
                    );
                    eq_factoring_checks!(
                        s_prime, t_prime, t, s, selected, literals, i, j
                    );
                }
                _ => {}
            }
        }
    }

    Err(format!(
        "Equality factoring cannot be applied to clause {:?} with picked literal {:?}",
        C, selected
    ))
}

#[allow(non_snake_case)]
pub fn superposition(
    C: &SupFormula,
    D: &SupFormula,
    selection_fn: &SelectionFunctionSignature,
) -> Result<(SupFormula, Substitution<SupTerm>), String> {
    let mut c_literals = unpack_literals(C)?;
    let mut d_literals = unpack_literals(D)?;
    let mut c_selected = selection_fn(&mut c_literals)?;
    let mut d_selected = selection_fn(&mut d_literals)?;

    macro_rules! sup_inference {
        ($l:expr, $r:expr, $other:expr, $i:expr, $j:expr) => {{
            // TODO: check `other` isnt an equality. in that case find_unifiable should only look in 1 term
            let unification_pair = find_unifiable_formula(&$other, $l);
            let (unification_pair, target, arg) = if unification_pair.is_some() {
                (unification_pair, $l, $r)
            } else {
                (find_unifiable_formula(&$other, $r), $r, $l)
            };

            if let Some((_, mgu)) = unification_pair {
                let other = formula_apply_substitution(&$other, &mgu);
                let target = term_apply_substitution(&target, &mgu);
                let other =
                    substitute_formula(&other, &target, &arg);
                let mut new_clause = vec![];
                new_clause.push(other);
                new_clause.extend(c_literals);
                new_clause.extend(d_literals);
                c_selected.remove($i);
                new_clause.extend(c_selected);
                d_selected.remove($j);
                new_clause.extend(d_selected);
                return Ok((formula_apply_substitution(&Clause(new_clause), &mgu), mgu));
            }
        }};
    }

    for i in 0..c_selected.len() {
        for j in 0..d_selected.len() {
            let c_lit = &c_selected[i];
            let d_lit = &d_selected[j];
            if let Equality(l, r) = c_lit {
                sup_inference!(l, r, d_lit, i, j);
            }
            if let Equality(l, r) = d_lit {
                sup_inference!(l, r, c_lit, i, j);
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
    use crate::config::SelectionFunction;
    use crate::type_theory::sup::inferences::{
        demodulate_first, eq_factoring, eq_resolution, factoring, resolution,
        subsumption_resolution_first, superposition,
    };
    use crate::type_theory::sup::sup::SupFormula::{
        Atom, Clause, Equality, Not,
    };
    use crate::type_theory::sup::sup::SupTerm::{Application, Variable};
    use crate::type_theory::sup::sup_utils::get_selection_fn;

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

    #[test]
    fn test_resolution() {
        let selection_fn = get_selection_fn(SelectionFunction::All());
        let p = Atom("P".to_string(), vec![Variable("x".to_string())]);
        let ligther = Atom("Q".to_string(), vec![]);
        let heavier = Atom(
            "R".to_string(),
            vec![Variable("x".to_string()), Variable("y".to_string())],
        );
        let not_p = Not(Box::new(p.clone()));

        assert!(
            matches!(
                resolution(&Clause(vec![p.clone()]), &Clause(vec![not_p.clone()]), &selection_fn),
                Ok((Clause(ref c), _)) if c.is_empty()
            ),
            "Resolution doesnt derive empty clause from contraddictory literals"
        );
        assert!(
            matches!(
                resolution(
                    &Clause(vec![p.clone(), ligther.clone()]),
                    &Clause(vec![not_p.clone()]),
                    &selection_fn
                ),
                Ok((Clause(ref lits), _)) if lits == &[ligther.clone()]
            ),
            "Resolution doesnt preserve unrelated literals from left clause"
        );
        assert!(
            matches!(
                resolution(
                    &Clause(vec![p.clone()]),
                    &Clause(vec![not_p.clone(), ligther.clone()]),
                    &selection_fn
                ),
                Ok((Clause(ref lits), _)) if lits == &[ligther.clone()]
            ),
            "Resolution doesnt preserve unrelated literals from right clause"
        );

        let maximal_selection = get_selection_fn(SelectionFunction::Maximal());
        assert!(
            resolution(&Clause(vec![p.clone(), heavier.clone()]), &Clause(vec![not_p.clone()]), &maximal_selection).is_err(),
            "Maximal literal according to KBO doesnt have a negation but resolution was applied regardless"
        );
    }

    #[test]
    fn test_resolution_unification() {
        let selection_fn = get_selection_fn(SelectionFunction::All());
        let x = Variable("x".to_string());
        let y = Variable("y".to_string());
        let z = Variable("z".to_string());
        let fx = Application("f".to_string(), vec![x.clone()]);
        let py = Atom("P".to_string(), vec![y.clone()]);
        let pfx = Atom("P".to_string(), vec![fx.clone()]);
        let qy = Atom("Q".to_string(), vec![y.clone(), z.clone()]);
        let ry = Atom("R".to_string(), vec![y.clone(), z.clone()]);
        let qfx = Atom("Q".to_string(), vec![fx.clone(), z.clone()]);
        let rfx = Atom("R".to_string(), vec![fx.clone(), z.clone()]);

        assert!(
            matches!(
                resolution(
                    &Clause(vec![py.clone(), qy.clone()]),
                    &Clause(vec![Not(Box::new(pfx.clone())), ry.clone()]),
                    &selection_fn
                ),
                Ok((Clause(ref c), _)) if c == &[qfx.clone(), rfx.clone()],
            ),
            "Resolution couldnt apply unification properly with negation over expanded body"
        );
        assert!(
            matches!(
                resolution(
                    &Clause(vec![Not(Box::new(py.clone())), qy.clone()]),
                    &Clause(vec![pfx.clone(), ry.clone()]),
                    &selection_fn
                ),
                Ok((Clause(ref c), _)) if c == &[rfx.clone(), qfx.clone()],
            ),
            "Resolution couldnt apply unification properly with negation over variable literal"
        );
    }

    #[test]
    fn test_factoring() {
        let selection_fn = get_selection_fn(SelectionFunction::All());
        let p = Atom("P".to_string(), vec![]);
        let q = Atom("Q".to_string(), vec![Variable("x".to_string())]);

        assert!(
            matches!(
                factoring(&Clause(vec![q.clone(), q.clone()]), &selection_fn),
                Ok((Clause(ref c), _)) if c == &[q.clone()],
            ),
            "Factoring rule didnt remove the duplicate predicate"
        );
        assert!(
            matches!(
                factoring(
                    &Clause(vec![q.clone(), p.clone(), q.clone()]),
                    &selection_fn
                ),
                Ok((Clause(ref c), _)) if c == &[q.clone(), p.clone()],
            ),
            "Factoring rule didnt keep the non selected predicate"
        );
        assert!(
            factoring(&Clause(vec![p.clone(), q.clone()]), &selection_fn)
                .is_err(),
            "Factoring rule applied with no unification available"
        );
    }

    #[test]
    fn test_factoring_resolution() {
        let selection_fn = get_selection_fn(SelectionFunction::All());
        let x = Variable("x".to_string());
        let y = Variable("y".to_string());
        let z = Variable("z".to_string());
        let fx = Application("f".to_string(), vec![x.clone()]);
        let py = Atom("P".to_string(), vec![y.clone()]);
        let pfx = Atom("P".to_string(), vec![fx.clone()]);
        let qy = Atom("Q".to_string(), vec![y.clone(), z.clone()]);
        let qfx = Atom("Q".to_string(), vec![fx.clone(), z.clone()]);

        let (derived, _) = factoring(
            &Clause(vec![py.clone(), pfx.clone(), qy.clone()]),
            &selection_fn,
        )
        .unwrap();
        assert_eq!(
            derived,
            Clause(vec![pfx.clone(), qfx.clone()]),
            "Factoring couldnt apply unification properly"
        )
    }

    #[test]
    fn test_eq_resolution() {
        let selection_fn = get_selection_fn(SelectionFunction::All());
        let t = Application("f".to_string(), vec![Variable("y".to_string())]);
        let s = Application(
            "f".to_string(),
            vec![Variable("y".to_string()), Variable("z".to_string())],
        );
        let neq_ss = Not(Box::new(Equality(s.clone(), s.clone())));
        let neq_st = Not(Box::new(Equality(s.clone(), t.clone())));
        let p = Atom("P".to_string(), vec![]);

        assert!(
            matches!(
                eq_resolution(&Clause(vec![neq_ss.clone()]), &selection_fn),
                Ok((Clause(ref c), _)) if c == &[],
            ),
            "Equality resolution didnt simplify clause with difference of identical terms"
        );
        assert!(
            matches!(
                eq_resolution(
                    &Clause(vec![neq_ss.clone(), p.clone()]),
                    &selection_fn
                ),
                Ok((Clause(ref c), _)) if c == &[p.clone()],
            ),
            "Equality resolution doesnt preserve unprocessed terms"
        );
        assert!(
            eq_resolution(&Clause(vec![neq_st.clone(), p.clone()]), &selection_fn).is_err(),
            "Equality resolution applied with no inconsistent unification available"
        );
    }

    #[test]
    fn test_eq_resolution_unification() {
        let selection_fn = get_selection_fn(SelectionFunction::All());
        let x = Variable("x".to_string());
        let y = Variable("y".to_string());
        let z = Variable("z".to_string());
        let fx = Application("f".to_string(), vec![x.clone()]);
        let py = Atom("P".to_string(), vec![y.clone(), z.clone()]);
        let pfx = Atom("P".to_string(), vec![fx.clone(), z.clone()]);
        let neq = Not(Box::new(Equality(y.clone(), fx.clone())));

        assert!(
            matches!(
                eq_resolution(
                    &Clause(vec![neq.clone(), py.clone()]),
                    &selection_fn
                ),
                Ok((Clause(ref c), _)) if c == &[pfx.clone()],
            ),
            "Factoring not applied properly with unification available"
        );
    }

    #[test]
    fn test_eq_factoring() {
        let selection_fn = get_selection_fn(SelectionFunction::All());
        let bigger = Application(
            "f".to_string(),
            vec![
                Variable("x".to_string()),
                Variable("y".to_string()),
                Variable("z".to_string()),
            ],
        );
        // unfiable corresponds to s and s' in the vampire paper, not testing unification here
        let unifiable = Application(
            "s".to_string(),
            vec![Variable("x".to_string()), Variable("y".to_string())],
        );
        // terms are constructed to enforce t < s and t' < t
        let t = Application("t".to_string(), vec![Variable("x".to_string())]);
        let t_prime = Variable("t_prime".to_string());
        let rest = Atom("P".to_string(), vec![]);

        assert!(
            matches!(
                eq_factoring(
                    &Clause(vec![
                        Equality(unifiable.clone(), t.clone()),
                        Equality(unifiable.clone(), t_prime.clone()),
                    ]),
                    &selection_fn
                ),
                Ok((Clause(ref c), _)) if c == &[
                    Equality(unifiable.clone(), t.clone()),
                    Not(Box::new(Equality(t.clone(), t_prime.clone()))),
                ],
            ),
            "Equality factoring isnt working as expected"
        );
        assert!(
            matches!(
                eq_factoring(
                    &Clause(vec![
                        Equality(t.clone(), unifiable.clone()),
                        Equality(unifiable.clone(), t_prime.clone()),
                    ]),
                    &selection_fn
                ),
                Ok((Clause(ref c), _)) if c == &[
                    Equality(t.clone(), unifiable.clone()), // keep this swap consistent with the arguments
                    Not(Box::new(Equality(t.clone(), t_prime.clone()))),
                ],
            ),
            "Equality factoring result depends on ordering of first equality (not even order-equivariant)"
        );
        assert!(
            matches!(
                eq_factoring(
                    &Clause(vec![
                        Equality(unifiable.clone(), t.clone()),
                        Equality(t_prime.clone(), unifiable.clone()),
                    ]),
                    &selection_fn
                ),
                Ok((Clause(ref c), _)) if c == &[
                    Equality(unifiable.clone(), t.clone()),
                    Not(Box::new(Equality(t.clone(), t_prime.clone()))),
                ],
            ),
            "Equality factoring result depends on ordering of second equality"
        );
        assert!(
            matches!(
                eq_factoring(
                    &Clause(vec![
                        Equality(unifiable.clone(), t_prime.clone()),
                        Equality(unifiable.clone(), t.clone()),
                    ]),
                    &selection_fn
                ),
                Ok((Clause(ref c), _)) if c == &[
                    Equality(unifiable.clone(), t.clone()),
                    Not(Box::new(Equality(t.clone(), t_prime.clone()))),
                ],
            ),
            "Equality factoring result depends on relative ordering of equality literals"
        );

        assert!(
            matches!(
                eq_factoring(
                    &Clause(vec![
                        Equality(unifiable.clone(), t.clone()),
                        Equality(unifiable.clone(), t_prime.clone()),
                        rest.clone()
                    ]),
                    &selection_fn
                ),
                Ok((Clause(ref c), _)) if c == &[
                    Equality(unifiable.clone(), t.clone()),
                    Not(Box::new(Equality(t.clone(), t_prime.clone()))),
                    rest.clone()
                ],
            ),
            "Equality factoring isnt preserving other literals"
        );
        assert!(
            eq_factoring(
                &Clause(vec![
                    Equality(unifiable.clone(), t.clone()),
                    Equality(unifiable.clone(), t.clone()),
                    rest.clone()
                ]),
                &selection_fn
            )
            .is_err(),
            "Equality factoring is passing with t' < t constraint violated"
        );
        assert!(
            eq_factoring(
                &Clause(vec![
                    Equality(unifiable.clone(), bigger.clone()),
                    Equality(unifiable.clone(), t_prime.clone()),
                    rest.clone()
                ]),
                &selection_fn
            )
            .is_err(),
            "Equality factoring is passing with t < s constraint violated"
        );
    }

    #[test]
    fn test_eq_factoring_unification() {
        let selection_fn = get_selection_fn(SelectionFunction::All());
        let k = Application("k".to_string(), vec![]);
        let k_prime = Application("k_prime".to_string(), vec![]);
        let s = Application(
            "s".to_string(),
            vec![Variable("x".to_string()), Variable("y".to_string())],
        );
        let s_prime =
            Application("s".to_string(), vec![k.clone(), k_prime.clone()]);
        // terms are constructed to enforce t < s and t' < t
        let tx = Application("t".to_string(), vec![Variable("x".to_string())]);
        let tk = Application("t".to_string(), vec![k.clone()]);
        let t_prime = Variable("t_prime".to_string());

        assert!(
            matches!(
                eq_factoring(
                    &Clause(vec![
                        Equality(s.clone(), tx.clone()),
                        Equality(s_prime.clone(), t_prime.clone())
                    ]),
                    &selection_fn
                ),
                Ok((Clause(ref c), _)) if c == &[
                    Equality(s_prime.clone(), tk.clone()),
                    Not(Box::new(Equality(tk.clone(), t_prime.clone())))
                ],
            ),
            "Equality resolution not applied properly with unification available"
        );
    }

    #[test]
    fn test_superposition() {
        let selection_fn = get_selection_fn(SelectionFunction::All());
        // unfiable corresponds to l and s in the vampire paper, not testing unification here
        let unifiable =
            Application("l".to_string(), vec![Variable("x".to_string())]);
        // terms are constructed to enforce r < l and t' < t[s]
        let r = Variable("r".to_string());
        let t_prime = Variable("t_prime".to_string());
        let t = Application("t".to_string(), vec![unifiable.clone()]);
        let t_subst = Application("t".to_string(), vec![r.clone()]);
        let p = Atom("L".to_string(), vec![unifiable.clone()]);
        let p_subst = Atom("L".to_string(), vec![r.clone()]);
        let q = Atom("Q".to_string(), vec![]);

        assert!(
            matches!(
                superposition(
                    &Clause(vec![Equality(unifiable.clone(), r.clone())]),
                    &Clause(vec![p.clone()]),
                    &selection_fn
                ),
                Ok((Clause(ref c), _)) if c == &[p_subst.clone()],
            ),
            "Superposition isnt working with predicates"
        );
        assert!(
            matches!(
                superposition(
                    &Clause(vec![Equality(unifiable.clone(), r.clone())]),
                    &Clause(vec![Equality(t.clone(), t_prime.clone())]),
                    &selection_fn
                ),
                Ok((Clause(ref c), _)) if c == &[Equality(t_subst.clone(), t_prime.clone())],
            ),
            "Superposition isnt working with equalities"
        );
        assert!(
            matches!(
                superposition(
                    &Clause(vec![Equality(unifiable.clone(), r.clone())]),
                    &Clause(vec![Not(Box::new(Equality(
                        t.clone(),
                        t_prime.clone()
                    )))]),
                    &selection_fn
                ),
                Ok((Clause(ref c), _)) if c == &[Not(Box::new(Equality(
                    t_subst.clone(),
                    t_prime.clone()
                )))],
            ),
            "Superposition isnt working with negated equalities"
        );
        assert!(
            matches!(
                superposition(
                    &Clause(vec![
                        Equality(unifiable.clone(), r.clone()),
                        Not(Box::new(q.clone()))
                    ]),
                    &Clause(vec![p.clone(), q.clone()]),
                    &selection_fn
                ),
                Ok((Clause(ref c), _)) if c == &[
                    p_subst.clone(),
                    Not(Box::new(q.clone())),
                    q.clone(),
                ],
            ),
            "Superposition isnt preserving unralted literals"
        );

        assert!(
            superposition(
                &Clause(vec![Equality(r.clone(), unifiable.clone())]),
                &Clause(vec![p.clone()]),
                &selection_fn
            )
            .is_ok(),
            "Superposition is dependent on equality terms ordering"
        );
        assert!(
            matches!(
                superposition(
                    &Clause(vec![p.clone()]),
                    &Clause(vec![Equality(unifiable.clone(), r.clone())]),
                    &selection_fn
                ),
                Ok((Clause(ref c), _)) if c == &[p_subst.clone()],
            ),
            "Superposition is dependent on clause ordering"
        );
    }

    #[test]
    fn test_superposition_unification() {
        let selection_fn = get_selection_fn(SelectionFunction::All());
        // expected mgu will be { x -> k }
        let x = Variable("x".to_string());
        let k = Application("k".to_string(), vec![]);
        let s = Application("f".to_string(), vec![k.clone()]);
        let l = Application("f".to_string(), vec![x.clone()]);
        let r = Application("r".to_string(), vec![]);
        let ps = Atom(
            "P".to_string(),
            vec![Application("c".to_string(), vec![]), s.clone()],
        );
        let pr = Atom(
            "P".to_string(),
            vec![Application("c".to_string(), vec![]), r.clone()],
        );
        let otherx = Atom("Q".to_string(), vec![x.clone()]);
        let otherk = Atom("Q".to_string(), vec![k.clone()]);

        assert!(
            matches!(
                superposition(
                    &Equality(l.clone(), r.clone()),
                    &Clause(vec![ps.clone(), otherx.clone()]),
                    &selection_fn
                ),
                Ok((Clause(ref c), _)) if c ==&[pr.clone(), otherk.clone()],
            ),
            "Superposition not applied properly with unification available"
        );
    }
}
