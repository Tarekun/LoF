use super::cic::CicTerm;
use super::cic::CicTerm::{
    Abstraction, Application, Match, Meta, Product, Sort, Variable,
};
use crate::type_theory::cic::cic::{Cic, GLOBAL_INDEX};
use crate::type_theory::cic::cic_utils::substitute_meta;
use crate::type_theory::environment::{Constraint, Environment};
use std::collections::{HashMap, VecDeque};

pub fn cic_unification(
    environment: &mut Environment<Cic>,
    term1: &CicTerm,
    term2: &CicTerm,
) -> Result<bool, String> {
    let mut constraints = environment.get_constraints();
    constraints.push(Constraint::TypeEq(term1.to_owned(), term2.to_owned()));
    Ok(solve_unification(constraints).is_ok())
}

pub fn instatiate_metas(
    term: &CicTerm,
    unifier: &HashMap<i32, CicTerm>,
) -> CicTerm {
    //TODO make this function efficient, this creates a quadratic cost
    let mut term = term.clone();
    for (index, body) in unifier {
        term = substitute_meta(&term, &index, &body);
    }
    term
}

pub fn solve_unification(
    constraints: Vec<Constraint<Cic>>,
) -> Result<HashMap<i32, CicTerm>, String> {
    fn occurs_check(meta_index: i32, term: &CicTerm) -> Result<(), String> {
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
                occurs_check(meta_index, arg_type)?;
                occurs_check(meta_index, body)
            }
            Product(_, arg_type, body) => {
                occurs_check(meta_index, arg_type)?;
                occurs_check(meta_index, body)
            }
            Application(left, right) => {
                occurs_check(meta_index, &left)?;
                occurs_check(meta_index, &right)
            }
            Match(matched, branches) => {
                for (pattern, body) in branches {
                    occurs_check(meta_index, pattern)?;
                    occurs_check(meta_index, body)?;
                }
                occurs_check(meta_index, &matched)
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
        occurs_check(index, &term)?;

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
                        constraints.push_back(Constraint::TypeEq(
                            (*left_matched_term).clone(),
                            (*right_matched_term).clone(),
                        ));

                        solver(constraints, substitution)
                    }
                    _ => error_obj,
                }
            }
        }
    }

    solver(constraints.into_iter().collect(), HashMap::new())
}

pub fn equal_under_substitution(
    environment: &mut Environment<Cic>,
    term1: &CicTerm,
    term2: &CicTerm,
) -> bool {
    match (term1, term2) {
        (Variable(name1, dbi1), Variable(name2, dbi2)) => {
            let mut res: bool = name1 == name2;

            if let Some((_, body)) = environment.get_from_deltas(&name1) {
                res = res || body == *term2;
            }
            if let Some((_, body)) = environment.get_from_deltas(&name2) {
                res = res || body == *term1;
            }
            //TODO probably i only need this
            res = res || *dbi1 == *dbi2;

            res
        }
        (Sort(name1), Sort(name2)) => name1 == name2,
        (Meta(index1), Meta(index2)) => index1 == index2,
        (Abstraction(_, domain1, body1), Abstraction(_, domain2, body2)) => {
            equal_under_substitution(environment, domain1, domain2)
                && equal_under_substitution(environment, body1, body2)
        }
        (Product(_, domain1, codomain1), Product(_, domain2, codomain2)) => {
            equal_under_substitution(environment, domain1, domain2)
                && equal_under_substitution(environment, codomain1, codomain2)
        }
        (Application(fun1, arg1), Application(fun2, arg2)) => {
            equal_under_substitution(environment, fun1, fun2)
                && equal_under_substitution(environment, arg1, arg2)
        }
        (Match(term1, pattern1), Match(term2, pattern2)) => {
            //TODO i dont want to do this now
            false
        }
        // terms arent structurally equal
        _ => false,
    }
}

#[cfg(test)]
mod unit_tests {
    use crate::type_theory::interface::TypeTheory;
    use crate::type_theory::{
        cic::{
            cic::{
                Cic,
                CicTerm::{Meta, Product, Sort, Variable},
                GLOBAL_INDEX,
            },
            unification::{equal_under_substitution, solve_unification},
        },
        environment::Constraint,
    };
    use std::collections::HashMap;

    #[test]
    fn test_dhm() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let constraints = vec![Constraint::TypeEq(Meta(0), nat.clone())];
        let expected = {
            let mut map = HashMap::new();
            map.insert(0, nat.clone());
            map
        };
        assert_eq!(
            solve_unification(constraints).unwrap(),
            expected,
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
    fn test_structurally_equal_terms() {}

    #[test]
    fn test_substitution() {
        let mut test_env = Cic::default_environment();
        test_env.add_substitution_with_type(
            "T",
            &Variable("Bool".to_string(), GLOBAL_INDEX),
            &Sort("TYPE".to_string()),
        );

        assert!(
            equal_under_substitution(
                &mut test_env,
                &Variable("T".to_string(), 0),
                &Variable("Bool".to_string(), GLOBAL_INDEX)
            ),
            "Equality up2 substitution refutes basic substitution check"
        );
    }

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
