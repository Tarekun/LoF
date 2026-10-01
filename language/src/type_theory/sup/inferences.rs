use crate::type_theory::commons::unification::Substitution;
use crate::type_theory::grammars::cnf::{
    CnfFormula::{self, Atom, Clause, Equality, ForAll, Not},
    CnfTerm::{self, Application, Variable},
};
use crate::type_theory::grammars::traits::Unification;
use crate::type_theory::interface::Automatic;
use crate::type_theory::sup::freedom::SelectionFunctionSignature;
use crate::type_theory::sup::sup::Sup;
use crate::type_theory::sup::sup_utils::{find_unifiable_formula, match_term};
use std::cmp::{
    max_by, min_by,
    Ordering::{Greater, Less},
};

//########################### SIMPLIFICATION INFERENCES
/// Rewrites every subterm of `term` that is an instance `from`σ of `from` to
/// `to`σ, as long as `to`σ is smaller. Subterms are rewritten before the
/// terms containing them
fn rewrite_term(term: &CnfTerm, from: &CnfTerm, to: &CnfTerm) -> CnfTerm {
    fn is_bound(term: &CnfTerm, σ: &Substitution<CnfTerm>) -> bool {
        match term {
            Variable(var) => σ.get(var).is_some(),
            Application(_, args) => args.iter().all(|arg| is_bound(arg, σ)),
        }
    }

    let term = match term {
        Application(fun, args) => Application(
            fun.to_string(),
            args.iter().map(|arg| rewrite_term(arg, from, to)).collect(),
        ),
        Variable(_) => term.clone(),
    };
    match match_term(from, &term) {
        // every variable of `to` must be bound, or the rewrite would
        // introduce new variables
        Some(σ) if is_bound(to, &σ) => {
            let rewritten = to.apply_substitution(&σ);
            if Sup::compare_terms(&term, &rewritten) == Greater {
                rewritten
            } else {
                term
            }
        }
        _ => term,
    }
}

fn rewrite_formula(
    φ: &CnfFormula,
    from: &CnfTerm,
    to: &CnfTerm,
) -> CnfFormula {
    let rewrite = |term: &CnfTerm| rewrite_term(term, from, to);
    match φ {
        Atom(pred, args) => {
            Atom(pred.to_string(), args.iter().map(rewrite).collect())
        }
        Equality(l, r) => Equality(rewrite(l), rewrite(r)),
        Not(ψ) => Not(Box::new(rewrite_formula(ψ, from, to))),
        Clause(literals) => Clause(
            literals
                .iter()
                .map(|literal| rewrite_formula(literal, from, to))
                .collect(),
        ),
        ForAll(var, var_type, body) => ForAll(
            var.to_string(),
            Box::new(rewrite_formula(var_type, from, to)),
            Box::new(rewrite_formula(body, from, to)),
        ),
    }
}

#[allow(non_snake_case)]
/// Applies a demodulation simplification rule to C,D, special case of superposition
/// inference where `D` is a unit equality `l = r`: every instance of either side
/// in `C` is rewritten to the matching instance of the other side, when smaller.
/// only the first argument `C` will be simplified
pub fn demodulate_first(C: &CnfFormula, D: &CnfFormula) -> CnfFormula {
    if let Equality(l, r) = D {
        // TODO also return mgu
        // TODO verify this is correct. the paper references the requirement of (l=r) > C
        let C = rewrite_formula(C, l, r);
        rewrite_formula(&C, r, l)
    } else {
        C.to_owned()
    }
}

#[allow(non_snake_case)]
/// Applies subsumption resolution inference simplifying the first argument `C`
pub fn subsumption_resolution_first(
    C: &CnfFormula,
    D: &CnfFormula,
) -> CnfFormula {
    // TODO also support/return mgu
    let c_lits = C.unpack_literals();
    let d_lits = D.unpack_literals();
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

            if Clause(d_new).subsumes(&Clause(c_new)) {
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

            if Clause(d_new).subsumes(&Clause(c_new)) {
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
    C: &CnfFormula,
    D: &CnfFormula,
    selection_fn: &SelectionFunctionSignature,
) -> (Vec<CnfFormula>, Substitution<CnfTerm>) {
    let mut c_literals = C.unpack_literals();
    let mut d_literals = D.unpack_literals();
    let c_selected = selection_fn(&mut c_literals);
    let d_selected = selection_fn(&mut d_literals);

    let mut newly_derived = vec![];
    let mut full_mgu = Substitution::empty();

    macro_rules! resolution_inference {
        ($c_idx:expr, $d_idx:expr, $c_selected:expr, $d_selected:expr, $c_others:expr, $d_others:expr) => {{
            match $c_selected[$c_idx] {
                Atom(_, _) => {
                    if let Not(inner) = &$d_selected[$d_idx] {
                        if let Ok(mgu) = $c_selected[$c_idx].unifies(inner) {
                            let mut new_clause = $c_selected.clone();
                            new_clause.remove($c_idx);
                            new_clause.extend($c_others.clone());

                            let mut d_selected = $d_selected.clone();
                            d_selected.remove($d_idx);
                            new_clause.extend(d_selected);
                            new_clause.extend($d_others.clone());

                            newly_derived.push(
                                Clause(new_clause).apply_substitution(&mgu),
                            );
                            full_mgu.merge(mgu);
                        }
                    }
                }
                _ => {}
            }
        }};
    }

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

    (newly_derived, full_mgu)
}

#[allow(non_snake_case)]
pub fn factoring(
    C: &CnfFormula,
    selection_fn: &SelectionFunctionSignature,
) -> (Vec<CnfFormula>, Substitution<CnfTerm>) {
    let mut literals = C.unpack_literals();
    let selected = selection_fn(&mut literals);

    let mut newly_derived = vec![];
    let mut full_mgu = Substitution::empty();

    for i in 0..selected.len() {
        for j in i + 1..selected.len() {
            if let Ok(mgu) = selected[i].unifies(&selected[j]) {
                let mut new_clause = selected.clone();
                new_clause.remove(j);
                new_clause.extend(literals.clone());

                newly_derived.push(Clause(new_clause).apply_substitution(&mgu));
                full_mgu.merge(mgu);
            }
        }
    }

    (newly_derived, full_mgu)
}

#[allow(non_snake_case)]
pub fn eq_resolution(
    C: &CnfFormula,
    selection_fn: &SelectionFunctionSignature,
) -> (Vec<CnfFormula>, Substitution<CnfTerm>) {
    let mut lits = C.unpack_literals();
    let selected = selection_fn(&mut lits);

    let mut newly_derived = vec![];
    let mut full_mgu = Substitution::empty();

    for i in 0..selected.len() {
        match &selected[i] {
            Not(boxed) => {
                if let Equality(l, r) = &**boxed {
                    if let Ok(mgu) = l.unifies(r) {
                        let mut new_clause = selected.clone();
                        new_clause.remove(i);
                        new_clause.extend(lits.clone());

                        newly_derived
                            .push(Clause(new_clause).apply_substitution(&mgu));
                        full_mgu.merge(mgu);
                    }
                }
            }
            _ => {}
        }
    }

    (newly_derived, full_mgu)
}

#[allow(non_snake_case)]
pub fn eq_factoring(
    C: &CnfFormula,
    selection_fn: &SelectionFunctionSignature,
) -> (Vec<CnfFormula>, Substitution<CnfTerm>) {
    let mut literals: Vec<CnfFormula> = C.unpack_literals();
    let selected = selection_fn(&mut literals);

    let mut newly_derived = vec![];
    let mut full_mgu = Substitution::empty();

    /// macro that checks for equality factoring appliability. it assumes that the macro is called
    /// from a clause in the form s=t ∨ s_prime=t_prime ∨ rest, where rest is a vector of atoms.
    /// it works symmetrically on the first equality by computing max=max(s,t) and min=min(s,t);
    /// then checks that min < max, max = s_prime, min < t_prime
    macro_rules! eq_factoring_checks {
        ($s:expr, $t:expr, $s_prime:expr, $t_prime:expr, $selected:expr, $unselected:expr, $i:expr, $j:expr) => {{
            // TODO check s/t arent isomorphic
            let max = max_by($s, $t, |a, b| Sup::compare_terms(a, b));
            let min = min_by($s, $t, |a, b| Sup::compare_terms(a, b));

            match (max.unifies($s_prime), Sup::compare_terms($t_prime, min)) {
                (Ok(mgu), Less) => {
                    let mut new_clause = selected.clone();
                    new_clause.remove($j);
                    new_clause.remove($i);
                    new_clause.extend($unselected.clone());

                    new_clause.push(Equality($s.to_owned(), $t.to_owned()));
                    new_clause.push(Not(Box::new(Equality(
                        min.to_owned(),
                        $t_prime.to_owned(),
                    ))));

                    newly_derived
                        .push(Clause(new_clause).apply_substitution(&mgu));
                    full_mgu.merge(mgu);
                }
                _ => {}
            }
        }};
    }

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

    (newly_derived, full_mgu)
}

#[allow(non_snake_case)]
pub fn superposition(
    C: &CnfFormula,
    D: &CnfFormula,
    selection_fn: &SelectionFunctionSignature,
) -> (Vec<CnfFormula>, Substitution<CnfTerm>) {
    let mut c_literals = C.unpack_literals();
    let mut d_literals = D.unpack_literals();
    let c_selected = selection_fn(&mut c_literals);
    let d_selected = selection_fn(&mut d_literals);
    let mut derived = vec![];
    let mut total_mgu = Substitution::empty();

    macro_rules! sup_inference {
        ($l:expr, $r:expr, $other:expr, $i:expr, $j:expr) => {{
            // TODO: check `other` isnt an equality. in that case find_unifiable should only look in 1 term
            let min = min_by($l, $r, |l, r| Sup::compare_terms(l, r));
            let max = max_by($l, $r, |l, r| Sup::compare_terms(l, r));
            let unification_pair = find_unifiable_formula(&$other, max);
            let target = max;
            let arg = min;

            if let Some((matched, mgu)) = unification_pair {
                // matched term must not be a variable
                if !matches!(matched, Variable(_)) {
                    let other = $other.apply_substitution(&mgu);
                    let target = target.apply_substitution(&mgu);
                    let other = other.substitute_formula(&target, &arg);
                    let mut new_clause = vec![];
                    new_clause.push(other);
                    new_clause.extend(c_literals.clone());
                    new_clause.extend(d_literals.clone());
                    let mut c_selected_clones = c_selected.clone();
                    c_selected_clones.remove($i);
                    new_clause.extend(c_selected_clones);
                    let mut d_selected_clones = d_selected.clone();
                    d_selected_clones.remove($j);
                    new_clause.extend(d_selected_clones);

                    derived.push(
                        Clause(new_clause).apply_substitution(&mgu),
                    );
                    total_mgu.merge(mgu);
                }
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

    (derived, total_mgu)
}
//########################### SUP INFERENCES

#[cfg(test)]
mod unit_tests {
    use crate::config::SelectionFunction;
    use crate::type_theory::grammars::cnf::{
        CnfFormula::{Atom, Clause, Equality, Not},
        CnfTerm::{self, Application, Variable},
    };
    use crate::type_theory::sup::freedom::get_selection_fn;
    use crate::type_theory::sup::inferences::{
        demodulate_first, eq_factoring, eq_resolution, factoring, resolution,
        subsumption_resolution_first, superposition,
    };
    use crate::type_theory::sup::sup_utils::with_answer_literal;

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
    fn test_demodulation_by_matching() {
        let var = |name: &str| Variable(name.to_string());
        let a = Application("a".to_string(), vec![]);
        let f = |t: CnfTerm| Application("f".to_string(), vec![t]);
        let g = |t: CnfTerm| Application("g".to_string(), vec![t]);
        let p = |t: CnfTerm| Atom("P".to_string(), vec![t]);
        let clause = Clause(vec![p(f(g(a.clone())))]);

        assert_eq!(
            demodulate_first(&clause, &Equality(f(g(var("X"))), var("X"))),
            Clause(vec![p(a.clone())]),
            "Demodulation doesnt rewrite instances of the greater side"
        );
        assert_eq!(
            demodulate_first(&clause, &Equality(var("X"), f(g(var("X"))))),
            Clause(vec![p(a.clone())]),
            "Demodulation doesnt rewrite by equalities whose greater side is on the right"
        );
        assert_eq!(
            demodulate_first(&clause, &Equality(f(var("X")), var("Y"))),
            clause,
            "Demodulation rewrites to a term with variables the match doesnt bind"
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
        let selection_fn = get_selection_fn(SelectionFunction::All);
        let p = Atom("P".to_string(), vec![Variable("x".to_string())]);
        let ligther = Atom("Q".to_string(), vec![]);
        let heavier = Atom(
            "R".to_string(),
            vec![Variable("x".to_string()), Variable("y".to_string())],
        );
        let not_p = Not(Box::new(p.clone()));

        let (derived, _) = resolution(
            &mut Clause(vec![p.clone()]),
            &mut Clause(vec![not_p.clone()]),
            &selection_fn,
        );
        assert_eq!(
            derived, vec![Clause(vec![])],
            "Resolution doesnt derive empty clause from contraddictory literals"
        );

        let (derived, _) = resolution(
            &mut Clause(vec![p.clone(), ligther.clone()]),
            &mut Clause(vec![not_p.clone()]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![ligther.clone()])],
            "Resolution doesnt preserve unrelated literals from left clause"
        );

        let (derived, _) = resolution(
            &mut Clause(vec![p.clone()]),
            &mut Clause(vec![not_p.clone(), ligther.clone()]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![ligther.clone()])],
            "Resolution doesnt preserve unrelated literals from right clause"
        );

        let maximal_selection = get_selection_fn(SelectionFunction::Maximal);
        let (derived, _) = resolution(
            &mut Clause(vec![p.clone(), heavier.clone()]),
            &mut Clause(vec![not_p.clone()]),
            &maximal_selection,
        );
        assert_eq!(
            derived,vec![],
            "Maximal literal according to KBO doesnt have a negation but resolution was applied regardless"
        );
    }

    #[test]
    fn test_resolution_unification() {
        let selection_fn = get_selection_fn(SelectionFunction::All);
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

        let (derived, _) = resolution(
            &mut Clause(vec![py.clone(), qy.clone()]),
            &mut Clause(vec![Not(Box::new(pfx.clone())), ry.clone()]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![qfx.clone(), rfx.clone()])],
            "Resolution couldnt apply unification properly with negation over expanded body"
        );

        let (derived, _) = resolution(
            &mut Clause(vec![Not(Box::new(py.clone())), qy.clone()]),
            &mut Clause(vec![pfx.clone(), ry.clone()]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![rfx.clone(), qfx.clone()])],
            "Resolution couldnt apply unification properly with negation over variable literal"
        );
    }

    #[test]
    fn test_factoring() {
        let selection_fn = get_selection_fn(SelectionFunction::All);
        let p = Atom("P".to_string(), vec![]);
        let q = Atom("Q".to_string(), vec![Variable("x".to_string())]);

        let (derived, _) =
            factoring(&mut Clause(vec![q.clone(), q.clone()]), &selection_fn);
        assert_eq!(
            derived,
            vec![Clause(vec![q.clone()])],
            "Factoring rule didnt remove the duplicate predicate"
        );

        let (derived, _) = factoring(
            &mut Clause(vec![q.clone(), p.clone(), q.clone()]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![q.clone(), p.clone()])],
            "Factoring rule didnt keep the non selected predicate"
        );

        let (derived, _) =
            factoring(&mut Clause(vec![p.clone(), q.clone()]), &selection_fn);
        assert_eq!(
            derived,
            vec![],
            "Factoring rule applied with no unification available"
        );
    }

    #[test]
    fn test_factoring_resolution() {
        let selection_fn = get_selection_fn(SelectionFunction::All);
        let x = Variable("x".to_string());
        let y = Variable("y".to_string());
        let z = Variable("z".to_string());
        let fx = Application("f".to_string(), vec![x.clone()]);
        let py = Atom("P".to_string(), vec![y.clone()]);
        let pfx = Atom("P".to_string(), vec![fx.clone()]);
        let qy = Atom("Q".to_string(), vec![y.clone(), z.clone()]);
        let qfx = Atom("Q".to_string(), vec![fx.clone(), z.clone()]);

        let (derived, _) = factoring(
            &mut Clause(vec![py.clone(), pfx.clone(), qy.clone()]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![pfx.clone(), qfx.clone()])],
            "Factoring couldnt apply unification properly"
        )
    }

    #[test]
    fn test_eq_resolution() {
        let selection_fn = get_selection_fn(SelectionFunction::All);
        let t = Application("f".to_string(), vec![Variable("y".to_string())]);
        let s = Application(
            "f".to_string(),
            vec![Variable("y".to_string()), Variable("z".to_string())],
        );
        let neq_ss = Not(Box::new(Equality(s.clone(), s.clone())));
        let neq_st = Not(Box::new(Equality(s.clone(), t.clone())));
        let p = Atom("P".to_string(), vec![]);

        let (derived, _) =
            eq_resolution(&mut Clause(vec![neq_ss.clone()]), &selection_fn);
        assert_eq!(
            derived,
            vec![Clause(vec![])],
            "Equality resolution didnt simplify clause with difference of identical terms"
        );

        let (derived, _) = eq_resolution(
            &mut Clause(vec![neq_ss.clone(), p.clone()]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![p.clone()])],
            "Equality resolution doesnt preserve unprocessed terms"
        );

        let (derived, _) = eq_resolution(
            &mut Clause(vec![neq_st.clone(), p.clone()]),
            &selection_fn,
        );
        assert_eq!(
            derived,vec![],
            "Equality resolution applied with no inconsistent unification available"
        );
    }

    #[test]
    fn test_eq_resolution_unification() {
        let selection_fn = get_selection_fn(SelectionFunction::All);
        let x = Variable("x".to_string());
        let y = Variable("y".to_string());
        let z = Variable("z".to_string());
        let fx = Application("f".to_string(), vec![x.clone()]);
        let py = Atom("P".to_string(), vec![y.clone(), z.clone()]);
        let pfx = Atom("P".to_string(), vec![fx.clone(), z.clone()]);
        let neq = Not(Box::new(Equality(y.clone(), fx.clone())));

        let (derived, _) = eq_resolution(
            &mut Clause(vec![neq.clone(), py.clone()]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![pfx.clone()])],
            "Factoring not applied properly with unification available"
        );
    }

    #[test]
    fn test_eq_factoring() {
        let selection_fn = get_selection_fn(SelectionFunction::All);
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

        // s(x,y)=t(x) ; s(x,y)=t' ⊦ s(x,y)=t(x) ; t(x)≠t'
        let (derived, _) = eq_factoring(
            &mut Clause(vec![
                Equality(unifiable.clone(), t.clone()),
                Equality(unifiable.clone(), t_prime.clone()),
            ]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![
                Equality(unifiable.clone(), t.clone()),
                Not(Box::new(Equality(t.clone(), t_prime.clone()))),
            ])],
            "Equality factoring isnt working as expected"
        );

        // t(x)=s(x,y) ; s(x,y)=t' ⊦ t(x)=s(x,y) ; t'≠t(x)
        let (derived, _) = eq_factoring(
            &mut Clause(vec![
                Equality(t.clone(), unifiable.clone()),
                Equality(unifiable.clone(), t_prime.clone()),
            ]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![
                    Equality(t.clone(), unifiable.clone()), // keep this swap consistent with the arguments
                    Not(Box::new(Equality(t.clone(), t_prime.clone()))),
                ])],
            "Equality factoring result depends on ordering of first equality (not even order-equivariant)"
        );

        // s(x,y)=t(x) ; t'=s(x,y) ⊦ s(x,y)=t(x) ; t(x)≠t'
        let (derived, _) = eq_factoring(
            &mut Clause(vec![
                Equality(unifiable.clone(), t.clone()),
                Equality(t_prime.clone(), unifiable.clone()),
            ]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![
                Equality(unifiable.clone(), t.clone()),
                Not(Box::new(Equality(t.clone(), t_prime.clone()))),
            ])],
            "Equality factoring result depends on ordering of second equality"
        );

        // s(x,y)=t' ; s(x,y)=t(x) ⊦ s(x,y)=t' ; t'≠t(x)
        let (derived, _) = eq_factoring(
            &mut Clause(vec![
                Equality(unifiable.clone(), t_prime.clone()),
                Equality(unifiable.clone(), t.clone()),
            ]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![
                    Equality(unifiable.clone(), t.clone()),
                    Not(Box::new(Equality(t.clone(), t_prime.clone()))),
                ])],
            "Equality factoring result depends on relative ordering of equality literals"
        );

        let (derived, _) = eq_factoring(
            &mut Clause(vec![
                Equality(unifiable.clone(), t.clone()),
                Equality(unifiable.clone(), t_prime.clone()),
                rest.clone(),
            ]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![
                rest.clone(),
                Equality(unifiable.clone(), t.clone()),
                Not(Box::new(Equality(t.clone(), t_prime.clone()))),
            ])],
            "Equality factoring isnt preserving other literals"
        );

        let (derived, _) = eq_factoring(
            &mut Clause(vec![
                Equality(unifiable.clone(), t.clone()),
                Equality(unifiable.clone(), t.clone()),
                rest.clone(),
            ]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![],
            "Equality factoring is passing with t' < t constraint violated"
        );

        let (derived, _) = eq_factoring(
            &mut Clause(vec![
                Equality(unifiable.clone(), bigger.clone()),
                Equality(unifiable.clone(), t_prime.clone()),
                rest.clone(),
            ]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![],
            "Equality factoring is passing with t < s constraint violated"
        );
    }

    #[test]
    fn test_eq_factoring_unification() {
        let selection_fn = get_selection_fn(SelectionFunction::All);
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

        let (derived, _) = eq_factoring(
            &mut Clause(vec![
                Equality(s.clone(), tx.clone()),
                Equality(s_prime.clone(), t_prime.clone()),
            ]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![
                    Equality(s_prime.clone(), tk.clone()),
                    Not(Box::new(Equality(tk.clone(), t_prime.clone())))
                ])],
            "Equality resolution not applied properly with unification available"
        );
    }

    #[test]
    fn test_eq_factoring_keeps_unselected() {
        let selection_fn = get_selection_fn(SelectionFunction::All);
        let s = Application("s".to_string(), vec![Variable("x".to_string())]);
        let t = Application("t".to_string(), vec![]);
        let t_prime = Variable("t_prime".to_string());
        // the answer literal is never selected, so it must be carried over as unselected
        let clause = with_answer_literal(&Clause(vec![
            Equality(s.clone(), t.clone()),
            Equality(s.clone(), t_prime.clone()),
        ]));
        let Clause(lits) = &clause else {
            panic!("expected a clause")
        };
        let answer = lits.last().unwrap().clone();

        let (derived, _) = eq_factoring(&clause, &selection_fn);
        assert_eq!(
            derived,
            vec![Clause(vec![
                answer.clone(),
                Equality(s.clone(), t.clone()),
                Not(Box::new(Equality(t.clone(), t_prime.clone()))),
            ])],
            "Equality factoring dropped the unselected literals"
        );
    }

    #[test]
    fn test_superposition() {
        let selection_fn = get_selection_fn(SelectionFunction::All);
        // unfiable corresponds to l and s in the vampire paper, not testing unification here
        let unifiable =
            Application("l".to_string(), vec![Variable("x".to_string())]);
        // terms are constructed to enforce r < l and t' < t[s]
        let r = Application("r".to_string(), vec![]);
        let t_prime = Variable("t'".to_string());
        let t = Application("t".to_string(), vec![unifiable.clone()]);
        let t_subst = Application("t".to_string(), vec![r.clone()]);
        let p = Atom("L".to_string(), vec![unifiable.clone()]);
        let p_subst = Atom("L".to_string(), vec![r.clone()]);
        let q = Atom("Q".to_string(), vec![]);

        // l(x)=r , L(l(x)) ⊦ L(r)
        let (derived, _) = superposition(
            &mut Clause(vec![Equality(unifiable.clone(), r.clone())]),
            &mut Clause(vec![p.clone()]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![p_subst.clone()])],
            "Superposition isnt working with predicates"
        );

        // l(x)=r , t(l(x))=t' ⊦ t(r)=t'
        let (derived, _) = superposition(
            &mut Clause(vec![Equality(unifiable.clone(), r.clone())]),
            &mut Clause(vec![Equality(t.clone(), t_prime.clone())]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![Equality(t_subst.clone(), t_prime.clone())])],
            "Superposition isnt working with equalities"
        );

        // l(x)=r , t(l(x))≠t' ⊦ t(r)≠t'
        let (derived, _) = superposition(
            &mut Clause(vec![Equality(unifiable.clone(), r.clone())]),
            &mut Clause(vec![Not(Box::new(Equality(
                t.clone(),
                t_prime.clone(),
            )))]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![Not(Box::new(Equality(
                t_subst.clone(),
                t_prime.clone()
            )))])],
            "Superposition isnt working with negated equalities"
        );

        // l(x)=r\/~Q , L(l(x))\/Q ⊦ L(r)\/~Q\/Q
        let (derived, _) = superposition(
            &mut Clause(vec![
                Equality(unifiable.clone(), r.clone()),
                Not(Box::new(q.clone())),
            ]),
            &mut Clause(vec![p.clone(), q.clone()]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![
                p_subst.clone(),
                Not(Box::new(q.clone())),
                q.clone(),
            ])],
            "Superposition isnt preserving unralted literals"
        );

        //
        let (derived, _) = superposition(
            &mut Clause(vec![Equality(r.clone(), unifiable.clone())]),
            &mut Clause(vec![p.clone()]),
            &selection_fn,
        );
        assert!(
            derived.len() > 0,
            "Superposition is dependent on equality terms ordering"
        );

        let (derived, _) = superposition(
            &mut Clause(vec![p.clone()]),
            &mut Clause(vec![Equality(unifiable.clone(), r.clone())]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![p_subst.clone()])],
            "Superposition is dependent on clause ordering"
        );
    }

    #[test]
    fn test_superposition_no_variable_rewriting() {
        // superposition must NOT fire when the only matching position
        let selection_fn = get_selection_fn(SelectionFunction::All);
        let x = Variable("x".to_string());
        let l = Application("l".to_string(), vec![]);
        let r = Application("r".to_string(), vec![]);

        // l=r , P(x) where x is a variable that can unify with l
        let (derived, _) = superposition(
            &mut Clause(vec![Equality(l.clone(), r.clone())]),
            &mut Clause(vec![Atom("P".to_string(), vec![x.clone()])]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![],
            "Superposition must not rewrite at a variable position"
        );

        let (derived, _) = superposition(
            &mut Clause(vec![Atom("P".to_string(), vec![x.clone()])]),
            &mut Clause(vec![Equality(l.clone(), r.clone())]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![],
            "Superposition must not rewrite at a variable position"
        );
    }

    #[test]
    fn test_superposition_unification() {
        let selection_fn = get_selection_fn(SelectionFunction::All);
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

        // f(x)=<r> , P(<c>, f(<k>))\/Q(x) ⊦ P(<c>, <r>)\/Q(<k>)
        let (derived, _) = superposition(
            &mut Equality(l.clone(), r.clone()),
            &mut Clause(vec![ps.clone(), otherx.clone()]),
            &selection_fn,
        );
        assert_eq!(
            derived,
            vec![Clause(vec![pr.clone(), otherk.clone()])],
            "Superposition not applied properly with unification available"
        );
    }
}
