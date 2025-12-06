use super::cic::CicTerm;
use super::cic::CicTerm::{
    Abstraction, Application, Let, Match, Meta, Product, Sort, Variable,
};
use crate::type_theory::cic::cic::{Cic, GLOBAL_INDEX};
use crate::type_theory::cic::cic_utils::{
    application_args, get_applied_function, substitute_meta,
};
use crate::type_theory::commons::unification::{unify, Substitution};
use crate::type_theory::environment::{Constraint, Environment};
use std::collections::{HashMap, VecDeque};

fn is_metavariable(term: &CicTerm) -> Option<String> {
    match term {
        Meta(idx) => Some(format!("{}", idx)),
        _ => None,
    }
}
fn structurally_equal(term1: &CicTerm, term2: &CicTerm) -> bool {
    match (term1, term2) {
        (Sort(_), Sort(_)) => true,
        (Meta(_), Meta(_)) => true,
        (Variable(name1, dbi1), Variable(name2, dbi2)) => {
            // same dbi1 and if they are global constants then also the constant symbols must be the same
            dbi1 == dbi2 && (*dbi1 != GLOBAL_INDEX || name1 == name2)
        }
        (Abstraction(_, type1, body1), Abstraction(_, type2, body2)) => {
            structurally_equal(type1, type2) && structurally_equal(body1, body2)
        }
        (Product(_, type1, body1), Product(_, type2, body2)) => {
            structurally_equal(type1, type2) && structurally_equal(body1, body2)
        }
        (Application(_, _), Application(_, _)) => {
            // TODO: review if this is enough/too much
            structurally_equal(
                &get_applied_function(term1),
                &get_applied_function(term2),
            ) && application_args(term1).len() == application_args(term2).len()
        }
        (Let(_, _, body1, scope1), Let(_, _, body2, scope2)) => {
            structurally_equal(body1, body2)
                && structurally_equal(scope1, scope2)
        }
        // TODO this explosion is order dependent on the branches, itd be nice to
        // reorder branches in some deterministic way
        (Match(matched1, branches1), Match(matched2, branches2)) => {
            if !structurally_equal(matched1, matched2) {
                return false;
            }
            for (b1, b2) in branches1.iter().zip(branches2.iter()) {
                let (pattern1, body1) = b1;
                let (pattern2, body2) = b2;
                if !(structurally_equal(pattern1, pattern2)
                    || structurally_equal(body1, body2))
                {
                    return false;
                }
            }
            true
        }
        _ => false,
    }
}
fn explode(term: &CicTerm) -> Vec<CicTerm> {
    match term {
        Abstraction(_, var_type, body) => {
            vec![(**var_type).to_owned(), (**body).to_owned()]
        }
        Product(_, var_type, body) => {
            vec![(**var_type).to_owned(), (**body).to_owned()]
        }
        Application(left, right) => {
            vec![(**left).to_owned(), (**right).to_owned()]
        }
        // TODO this explosion is order dependent on the branches, itd be nice to
        // reorder branches in some deterministic way
        Match(matched_term, branches) => {
            let mut subexpressions = vec![(**matched_term).to_owned()];
            for (pattern, body) in branches {
                subexpressions.push(pattern.to_owned());
                subexpressions.push(body.to_owned());
            }
            subexpressions
        }
        // TODO figure out what to do with opt_type
        Let(_, opt_type, body, scope) => {
            vec![(**body).to_owned(), (**scope).to_owned()]
        }
        _ => vec![],
    }
}
fn occurs_meta_check(meta_index: i32, term: &CicTerm) -> Result<(), String> {
    match term {
        Meta(index) => {
            if meta_index == *index {
                Err("Unification Failure: cyclical metavariable reference"
                    .to_string())
            } else {
                Ok(())
            }
        }
        Abstraction(_, arg_type, body) => {
            occurs_meta_check(meta_index, arg_type)?;
            occurs_meta_check(meta_index, body)
        }
        Product(_, arg_type, body) => {
            occurs_meta_check(meta_index, arg_type)?;
            occurs_meta_check(meta_index, body)
        }
        Application(left, right) => {
            occurs_meta_check(meta_index, &left)?;
            occurs_meta_check(meta_index, &right)
        }
        Match(matched, branches) => {
            for (pattern, body) in branches {
                occurs_meta_check(meta_index, pattern)?;
                occurs_meta_check(meta_index, body)?;
            }
            occurs_meta_check(meta_index, &matched)
        }
        Let(_, opt_type, body, scope) => {
            if let Some(typ) = &**opt_type {
                occurs_meta_check(meta_index, typ)?;
            }
            occurs_meta_check(meta_index, body)?;
            occurs_meta_check(meta_index, scope)
        }
        _ => Ok(()),
    }
}
fn occurs(term: &CicTerm, name: &str) -> bool {
    occurs_meta_check(name.parse().unwrap(), term).is_err()
}

/// Second order unification of meta-variable for type inference
pub fn cic_so_unification(
    term1: &CicTerm,
    term2: &CicTerm,
) -> Result<Substitution<CicTerm>, String> {
    Ok(unify(
        term1,
        term2,
        is_metavariable,
        structurally_equal,
        explode,
        occurs,
    )?
    .reduce(|term, idx, arg| substitute_meta(term, &idx.parse().unwrap(), arg)))
}

pub fn cic_unification(
    _: &mut Environment<Cic>,
    term1: &CicTerm,
    term2: &CicTerm,
) -> Result<bool, String> {
    Ok(cic_so_unification(term1, term2).is_ok())
}

// TODO fully get rid of this function. nowhere in the code this should be used
pub fn solve_unification(
    constraints: Vec<Constraint<Cic>>,
) -> Result<HashMap<i32, CicTerm>, String> {
    fn occurs_meta_check(
        meta_index: i32,
        term: &CicTerm,
    ) -> Result<(), String> {
        match term {
            Meta(index) => {
                if meta_index == *index {
                    Err("Unification Failure: cyclical metavariable reference"
                        .to_string())
                } else {
                    Ok(())
                }
            }
            Abstraction(_, arg_type, body) => {
                occurs_meta_check(meta_index, arg_type)?;
                occurs_meta_check(meta_index, body)
            }
            Product(_, arg_type, body) => {
                occurs_meta_check(meta_index, arg_type)?;
                occurs_meta_check(meta_index, body)
            }
            Application(left, right) => {
                occurs_meta_check(meta_index, &left)?;
                occurs_meta_check(meta_index, &right)
            }
            Match(matched, branches) => {
                for (pattern, body) in branches {
                    occurs_meta_check(meta_index, pattern)?;
                    occurs_meta_check(meta_index, body)?;
                }
                occurs_meta_check(meta_index, &matched)
            }
            _ => Ok(()),
        }
    }

    fn handle_meta(
        index: i32,
        term: &CicTerm,
        substitution: HashMap<i32, CicTerm>,
    ) -> Result<HashMap<i32, CicTerm>, String> {
        if let Meta(_) = term {
            return Err("TF am i supposed todo with this?".to_string());
        }
        occurs_meta_check(index, &term)?;

        // this update introduces a quadratic cost in the overall algo
        let mut substitution: HashMap<i32, CicTerm> = substitution
            .iter()
            .map(|(k, v)| (*k, substitute_meta(v, &index, &term)))
            .collect();
        substitution.insert(index, term.clone());
        Ok(substitution)
    }

    fn missmatch_error(
        left: &CicTerm,
        right: &CicTerm,
    ) -> Result<HashMap<i32, CicTerm>, String> {
        Err(format!(
            "Unification failed: {:?} and {:?} don't unify",
            left, right
        ))
    }

    fn solver(
        mut constraints: VecDeque<Constraint<Cic>>,
        substitution: HashMap<i32, CicTerm>,
    ) -> Result<HashMap<i32, CicTerm>, String> {
        match constraints.len() {
            0 => Ok(substitution),
            _ => {
                let (left, right) = match constraints.pop_front().unwrap() {
                    Constraint::TypeEq(left, right) => (left, right),
                };
                let error_obj = missmatch_error(&left, &right);
                match (left, right) {
                    (Meta(index), right) => solver(
                        constraints,
                        handle_meta(index, &right, substitution)?,
                    ),
                    (left, Meta(index)) => solver(
                        constraints,
                        handle_meta(index, &left, substitution)?,
                    ),
                    (
                        Variable(left_name, left_dbi),
                        Variable(right_name, right_dbi),
                    ) => {
                        if (left_dbi != right_dbi)
                            || (left_dbi == GLOBAL_INDEX
                                && left_name != right_name)
                        {
                            return error_obj;
                        } else {
                            solver(constraints, substitution)
                        }
                    }
                    (Sort(left_sort), Sort(right_sort)) => {
                        //TODO support universes/subtypes
                        if left_sort != right_sort {
                            return error_obj;
                        } else {
                            solver(constraints, substitution)
                        }
                    }
                    (
                        Abstraction(_, left_arg_type, left_body),
                        Abstraction(_, right_arg_type, right_body),
                    ) => {
                        //TODO add eta reduction like in matita?
                        constraints.push_back(Constraint::TypeEq(
                            *left_arg_type,
                            *right_arg_type,
                        ));
                        constraints.push_back(Constraint::TypeEq(
                            *left_body,
                            *right_body,
                        ));
                        solver(constraints, substitution)
                    }
                    (
                        Product(_, left_arg_type, left_body),
                        Product(_, right_arg_type, right_body),
                    ) => {
                        constraints.push_back(Constraint::TypeEq(
                            *left_arg_type,
                            *right_arg_type,
                        ));
                        constraints.push_back(Constraint::TypeEq(
                            *left_body,
                            *right_body,
                        ));
                        solver(constraints, substitution)
                    }
                    (
                        Application(left_fun, left_arg),
                        Application(right_fun, right_arg),
                    ) => {
                        constraints.push_back(Constraint::TypeEq(
                            *left_fun, *right_fun,
                        ));
                        constraints.push_back(Constraint::TypeEq(
                            *left_arg, *right_arg,
                        ));
                        solver(constraints, substitution)
                    }
                    //TODO figure out what to do with branches
                    (
                        Match(left_matched_term, left_branches),
                        Match(right_matched_term, right_branches),
                    ) => {
                        if left_branches.len() != right_branches.len() {
                            return error_obj;
                        }

                        constraints.push_back(Constraint::TypeEq(
                            (*left_matched_term).clone(),
                            (*right_matched_term).clone(),
                        ));
                        // for unification to work here constructor branch ordering must be the same
                        // TODO would be nice to have match unification be independent of branch ordering
                        for i in 0..left_branches.len() {
                            let (left_pattern, left_body) = &left_branches[i];
                            let (right_pattern, right_body) =
                                &right_branches[i];
                            constraints.push_back(Constraint::TypeEq(
                                left_pattern.clone(),
                                right_pattern.clone(),
                            ));
                            constraints.push_back(Constraint::TypeEq(
                                left_body.clone(),
                                right_body.clone(),
                            ));
                        }

                        solver(constraints, substitution)
                    }
                    _ => error_obj,
                }
            }
        }
    }

    solver(constraints.into_iter().collect(), HashMap::new())
}

#[cfg(test)]
mod unit_tests {
    use crate::type_theory::cic::unification::{
        cic_so_unification, solve_unification,
    };
    use crate::type_theory::commons::unification::Substitution;
    use crate::type_theory::{
        cic::cic::{
            Cic,
            CicTerm::{Match, Meta, Product, Sort, Variable},
            GLOBAL_INDEX,
        },
        environment::Constraint::{self, TypeEq},
    };
    use std::collections::HashMap;

    #[test]
    fn test_dhm() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        assert_eq!(
            cic_so_unification(&Meta(0), &nat).unwrap(),
            Substitution::from([("0".to_string(), nat.clone())]),
            "Unification couldnt solve one simple constraint"
        );

        let constraints = vec![
            Constraint::TypeEq(
                Meta(1),
                Product(
                    "_".to_string(),
                    Box::new(nat.clone()),
                    Box::new(Meta(0)),
                ),
            ),
            Constraint::TypeEq(Meta(0), nat.clone()),
        ];
        let expected = {
            let mut map = HashMap::new();
            map.insert(
                1,
                Product(
                    "_".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ),
            );
            map.insert(0, nat.clone());
            map
        };
        assert_eq!(
                solve_unification(constraints).unwrap(),
                expected,
                "Unification couldnt solve a problem with a function over metavariables"
            );
    }

    #[test]
    fn test_match_unification() {
        let t = Variable("true".to_string(), GLOBAL_INDEX);
        let expected = {
            let mut map = HashMap::new();
            map.insert(1, t.clone());
            map
        };
        let constraints = vec![TypeEq(
            Match(
                Box::new(Variable("b".to_string(), 0)),
                vec![
                    (t.clone(), Variable("b".to_string(), GLOBAL_INDEX)),
                    (
                        Variable("false".to_string(), GLOBAL_INDEX),
                        Variable("b".to_string(), GLOBAL_INDEX),
                    ),
                ],
            ),
            Match(
                Box::new(Variable("b".to_string(), 0)),
                vec![
                    (Meta(1), Variable("b".to_string(), GLOBAL_INDEX)),
                    (
                        Variable("false".to_string(), GLOBAL_INDEX),
                        Variable("b".to_string(), GLOBAL_INDEX),
                    ),
                ],
            ),
        )];
        assert_eq!(
            solve_unification(constraints).unwrap(),
            expected,
            "Unification couldnt solve a problem of constructor recovery in pattern matching"
        );

        let body = Sort("TYPE".to_string());
        let expected = {
            let mut map = HashMap::new();
            map.insert(2, body.clone());
            map
        };
        let constraints = vec![TypeEq(
            Match(
                Box::new(Variable("b".to_string(), 0)),
                vec![
                    (Variable("true".to_string(), GLOBAL_INDEX), body.clone()),
                    (Variable("false".to_string(), GLOBAL_INDEX), body.clone()),
                ],
            ),
            Match(
                Box::new(Variable("b".to_string(), 0)),
                vec![
                    (Variable("true".to_string(), GLOBAL_INDEX), Meta(2)),
                    (Variable("false".to_string(), GLOBAL_INDEX), body.clone()),
                ],
            ),
        )];
        assert_eq!(
            solve_unification(constraints).unwrap(),
            expected,
            "Unification couldnt solve unification of pattern match bodies"
        );
    }

    #[test]
    fn test_structurally_equal_terms() {}

    #[test]
    fn test_aplha_with_substitution() {
        //TODO: in principle this test is interesting: it tests that unification
        //can find a solution by performing -reduction
        //however i want to approach this in a different way with a controllable
        //number of reduction steps to perform on terms, rather than ad hoc swappings
        //with variables when unification fails

        // let mut test_env = Cic::default_environment();
        // test_env.add_substitution_with_type(
        //     "T",
        //     &Variable("Nat".to_string(), GLOBAL_INDEX),
        //     &Sort("TYPE".to_string()),
        // );

        // assert_eq!(
        //     cic_unification(
        //         &mut test_env,
        //         &Product(
        //             "_".to_string(),
        //             Box::new(Variable("Unit".to_string(), GLOBAL_INDEX)),
        //             Box::new(Variable("T".to_string(), GLOBAL_INDEX)),
        //         ),
        //         &Product(
        //             "x".to_string(),
        //             Box::new(Variable("Unit".to_string(), GLOBAL_INDEX)),
        //             Box::new(Variable("Nat".to_string(), GLOBAL_INDEX)),
        //         ),
        //     ),
        //     Ok(true),
        //     "Equality up2 substitution refutes substitution check over codomains of functions"
        // );

        // assert!(
        //     Cic::terms_unify(
        //         &mut test_env,
        //         &Product(
        //             "_".to_string(),
        //             Box::new(Variable("Unit".to_string(), GLOBAL_INDEX)),
        //             Box::new(Variable("T".to_string(), GLOBAL_INDEX)),
        //         ),
        //         &Product(
        //             "x".to_string(),
        //             Box::new(Variable("Unit".to_string(), GLOBAL_INDEX)),
        //             Box::new(Variable("Nat".to_string(), GLOBAL_INDEX)),
        //         ),
        //     ),
        //     "Equality up2 substitution refutes substitution check over codomains of functions"
        // );
    }
}
