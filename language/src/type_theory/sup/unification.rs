#[cfg(test)]
mod unit_tests {
    use crate::type_theory::{
        commons::unification::Substitution,
        grammars::{
            cnf::{
                CnfFormula::{Atom, Clause, Equality, Not},
                CnfTerm::{Application, Variable},
            },
            traits::Unification,
        },
    };

    #[test]
    fn test_term_unification() {
        let x = Variable("x".to_string());
        let y = Variable("y".to_string());
        let fx = Application("f".to_string(), vec![x.clone()]);
        let ffx = Application("f".to_string(), vec![fx.clone()]);

        assert!(
            x.unifies(&x).is_ok(),
            "Identical variable terms arent unified"
        );
        assert!(
            fx.unifies(&fx).is_ok(),
            "Identical application terms arent unified"
        );

        assert_eq!(
            Application("f".to_string(), vec![y.clone()]).unifies(&fx),
            Ok(Substitution::from([("y".to_string(), x.clone())])),
            "Unification didnt produce the proper MGU"
        );
        assert_eq!(
            Application("f".to_string(), vec![y.clone()]).unifies(&ffx),
            Ok(Substitution::from([("y".to_string(), fx.clone())])),
            "Unification didnt produce the proper MGU with deeper structure"
        );

        assert!(
            fx.unifies(&Application(
                "f".to_string(),
                vec![x.clone(), y.clone()]
            ))
            .is_err(),
            "Unifiable terms pass unification checks"
        );
        assert!(
            Application("f".to_string(), vec![x.clone()])
                .unifies(&ffx)
                .is_err(),
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
            s.unifies(&t),
            Ok(Substitution::from([
                ("y".to_string(), k.clone()),
                (
                    "x".to_string(),
                    Application("f".to_string(), vec![k.clone()])
                )
            ])),
            // TODO: im not really sure this should be enforced at the terms_unify but whatever for now
            "Returned MGU didnt solve variable `y` to constant `k` in assignment for variable `x`"
        )
    }

    #[test]
    fn test_formula_unification() {
        let x = Variable("x".to_string());
        let y = Variable("y".to_string());
        // let y = Variable("z".to_string());
        let fx = Application("f".to_string(), vec![x.clone()]);

        assert!(
            Atom("P".to_string(), vec![y.clone()])
                .unifies(&Atom("P".to_string(), vec![y.clone()]))
                .is_ok(),
            "Identical predicates dont unify"
        );
        assert!(
            Not(Box::new(Atom("P".to_string(), vec![y.clone()])))
                .unifies(&Not(Box::new(Atom(
                    "P".to_string(),
                    vec![fx.clone()]
                ))))
                .is_ok(),
            "Simple 1-step unification didnt pass"
        );
        assert!(
            Clause(vec![
                Atom("P".to_string(), vec![y.clone()]),
                Not(Box::new(Atom("P".to_string(), vec![y.clone()])))
            ])
            .unifies(&Clause(vec![
                Atom("P".to_string(), vec![y.clone()]),
                Not(Box::new(Atom("P".to_string(), vec![fx.clone()])))
            ]))
            .is_ok(),
            "Single formula-unification passed, but failed when inside a clause"
        );
        assert_eq!(
            Equality(Application("k".to_string(), vec![]), fx.clone()).unifies(
                &Equality(Application("k".to_string(), vec![]), y.clone())
            ),
            Ok(Substitution::from([("y".to_string(), fx.clone())])),
            "Unification didnt produce the proper MGU"
        );
    }
}
