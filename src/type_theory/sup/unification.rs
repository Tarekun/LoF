use crate::type_theory::fol::fol::FolFormula;
use crate::type_theory::interface::TypeTheory;
use crate::type_theory::sup::sup::Sup;
use crate::type_theory::sup::sup_utils::substitute_term;
use crate::type_theory::sup::{
    sup::{
        SupFormula::{self, Atom, Clause, Equality, ForAll, Not},
        SupTerm::{self, Application, Variable},
    },
    sup_utils::contains,
};
use std::collections::HashMap;

type Substitution = HashMap<String, SupTerm>;

pub fn terms_unify(
    term1: &SupTerm,
    term2: &SupTerm,
) -> Result<Substitution, String> {
    return terms_unify_impl(term1, term2, &mut HashMap::new());
}

pub fn formulas_unify(
    phi: &SupFormula,
    psi: &SupFormula,
) -> Result<Substitution, String> {
    fn solver(
        phi: &SupFormula,
        psi: &SupFormula,
        mgu: &mut Substitution,
    ) -> Result<Substitution, String> {
        let error = Err(format!(
            "Formulas {:?} and {:?} could not be unified",
            phi, psi
        ));
        match (phi, psi) {
            (Atom(p1, args1), Atom(p2, args2)) => {
                // TODO: do predicate names *must* be equal?
                if p1 != p2 || args1.len() != args2.len() {
                    return error;
                }

                for i in 0..args1.len() {
                    terms_unify_impl(&args1[i], &args2[i], mgu)?;
                }
            }
            (Not(phi), Not(psi)) => {
                solver(phi, psi, mgu)?;
            }
            (Equality(s, t), Equality(l, r)) => {
                terms_unify_impl(s, l, mgu)?;
                terms_unify_impl(t, r, mgu)?;
            }
            (Clause(lits1), Clause(lits2)) => {
                if lits1.len() != lits2.len() {
                    return error;
                }
                for i in 0..lits1.len() {
                    solver(&lits1[i], &lits2[i], mgu)?;
                }
            }
            (
                ForAll(var_name1, var_type1, body1),
                ForAll(var_name2, var_type2, body2),
            ) => {
                if var_name1 != var_name2 {
                    return error;
                }
                solver(var_type1, var_type2, mgu)?;
                solver(body1, body2, mgu)?;
            }

            _ => {
                return error;
            }
        }

        Ok(mgu.to_owned())
    }

    solver(phi, psi, &mut HashMap::new())
}

fn terms_unify_impl(
    term1: &SupTerm,
    term2: &SupTerm,
    mgu: &mut Substitution,
) -> Result<Substitution, String> {
    let error = Err(format!(
        "Terms {:?} and {:?} could not be unified",
        term1, term2
    ));

    fn add_substitution(
        var_name: &str,
        body: &SupTerm,
        mgu: &mut Substitution,
    ) -> Result<(), String> {
        let var_term = &Variable(var_name.to_string());
        if Sup::base_term_equality(body, var_term).is_ok() {
            // avoid failing on x=x but do not generate useless assignment
            return Ok(());
        }
        if contains(body, var_term) {
            // occurs check
            return Err(format!(
                "Substitution body {:?} contains a reference to variable {:?}",
                body, var_term
            ));
        }

        *mgu = mgu
            .iter()
            .map(|(k, v)| {
                (
                    k.to_string(),
                    substitute_term(v, &Variable(var_name.to_string()), body),
                )
            })
            .collect();
        mgu.insert(var_name.to_string(), body.clone());
        return Ok(());
    }

    match (term1, term2) {
        // TODO: add occurs check
        (Variable(var_name), _) => {
            add_substitution(var_name, term2, mgu)?;
        }
        (_, Variable(var_name)) => {
            add_substitution(var_name, term1, mgu)?;
        }
        (Application(f1, args1), Application(f2, args2)) => {
            // TODO: do function names *must* be equal?
            if f1 != f2 || args1.len() != args2.len() {
                return error;
            }

            for i in 0..args1.len() {
                terms_unify_impl(&args1[i], &args2[i], mgu)?;
            }
        }
        _ => {
            return error;
        }
    }

    Ok(mgu.to_owned())
}

pub fn term_apply_substitution(
    term: &SupTerm,
    substitution: &Substitution,
) -> SupTerm {
    match term {
        Variable(var_name) => {
            substitution.get(var_name).unwrap_or(term).clone()
        }
        Application(fun_name, args) => Application(
            fun_name.to_string(),
            args.iter()
                .map(|t| term_apply_substitution(t, substitution))
                .collect(),
        ),
    }
}
pub fn formula_apply_substitution(
    formula: &SupFormula,
    substitution: &Substitution,
) -> SupFormula {
    match formula {
        Atom(pred_name, args) => Atom(
            pred_name.to_string(),
            args.iter()
                .map(|t| term_apply_substitution(t, substitution))
                .collect(),
        ),
        Equality(l, r) => Equality(
            term_apply_substitution(l, substitution),
            term_apply_substitution(r, substitution),
        ),
        Not(f) => Not(Box::new(formula_apply_substitution(f, substitution))),
        Clause(lits) => Clause(
            lits.iter()
                .map(|l| formula_apply_substitution(l, substitution))
                .collect(),
        ),
        ForAll(var_name, var_type, body) => ForAll(
            var_name.to_string(),
            Box::new(formula_apply_substitution(var_type, substitution)),
            Box::new(formula_apply_substitution(body, substitution)),
        ),
    }
}

#[cfg(test)]
mod unit_tests {
    use crate::type_theory::sup::{
        sup::{
            SupFormula::{Atom, Clause, Equality, Not},
            SupTerm::{Application, Variable},
        },
        unification::{formulas_unify, terms_unify},
    };
    use std::collections::HashMap;

    #[test]
    fn test_term_unification() {
        let x = Variable("x".to_string());
        let y = Variable("y".to_string());
        let fx = Application("f".to_string(), vec![x.clone()]);
        let ffx = Application("f".to_string(), vec![fx.clone()]);

        assert!(
            terms_unify(&x, &x).is_ok(),
            "Identical variable terms arent unified"
        );
        assert!(
            terms_unify(&fx, &fx).is_ok(),
            "Identical application terms arent unified"
        );

        assert_eq!(
            terms_unify(&Application("f".to_string(), vec![y.clone()]), &fx),
            Ok(HashMap::from([("y".to_string(), x.clone())])),
            "Unification didnt produce the proper MGU"
        );
        assert_eq!(
            terms_unify(&Application("f".to_string(), vec![y.clone()]), &ffx),
            Ok(HashMap::from([("y".to_string(), fx.clone())])),
            "Unification didnt produce the proper MGU with deeper structure"
        );

        assert!(
            terms_unify(
                &fx,
                &Application("f".to_string(), vec![x.clone(), y.clone()])
            )
            .is_err(),
            "Unifiable terms pass unification checks"
        );
        assert!(
            terms_unify(&Application("f".to_string(), vec![x.clone()]), &ffx).is_err(),
            "Unification passes on substitution that dont pass the occurs check"
        );
    }

    #[test]
    fn test_fully_solved_mgu() {
        let x = Variable("x".to_string());
        let y = Variable("y".to_string());
        let fy = Application("f".to_string(), vec![y.clone()]);
        let k = Application("k".to_string(), vec![]);
        let s =
            Application("container".to_string(), vec![x.clone(), y.clone()]);
        let t =
            Application("container".to_string(), vec![fy.clone(), k.clone()]);

        assert_eq!(
            terms_unify(&s, &t),
            Ok(HashMap::from([
                ("y".to_string(), k.clone()),
                (
                    "x".to_string(),
                    Application("f".to_string(), vec![k.clone()])
                )
            ])),
            "Returned MGU didnt solve variable `y` to constant `k` in assignment for variable `x`"
        )
    }

    #[test]
    fn test_formula_unification() {
        let x = Variable("x".to_string());
        let y = Variable("y".to_string());
        // let y = Variable("z".to_string());
        let fx = Application("f".to_string(), vec![x.clone()]);
        let ffx = Application("f".to_string(), vec![fx.clone()]);

        assert!(
            formulas_unify(
                &Atom("P".to_string(), vec![y.clone()]),
                &Atom("P".to_string(), vec![y.clone()])
            )
            .is_ok(),
            "Identical predicates dont unify"
        );
        assert!(
            formulas_unify(
                &Not(Box::new(Atom("P".to_string(), vec![y.clone()]))),
                &Not(Box::new(Atom("P".to_string(), vec![fx.clone()]))),
            )
            .is_ok(),
            "Simple 1-step unification didnt pass"
        );
        assert!(
            formulas_unify(
                &Clause(vec![
                    Atom("P".to_string(), vec![y.clone()]),
                    Not(Box::new(Atom("P".to_string(), vec![y.clone()])))
                ]),
                &Clause(vec![
                    Atom("P".to_string(), vec![y.clone()]),
                    Not(Box::new(Atom("P".to_string(), vec![fx.clone()])))
                ])
            ).is_ok(),
            "Single formula-unification passed, but failed when inside a clause"
        );
        assert_eq!(
            formulas_unify(
                &Equality(Application("k".to_string(), vec![]), fx.clone()),
                &Equality(Application("k".to_string(), vec![]), y.clone())
            ),
            Ok(HashMap::from([("y".to_string(), fx.clone())])),
            "Unification didnt produce the proper MGU"
        );
    }
}
