use super::cic::CicTerm;
use super::cic::CicTerm::{
    Abstraction, Application, Let, Match, Meta, Product, Sort, Variable,
};
use crate::error::LofError;
use crate::type_theory::cic::cic::{Cic, GLOBAL_INDEX};
use crate::type_theory::cic::cic_utils::{
    application_args, get_applied_function, get_arg_types, is_constant,
    substitute_meta,
};
use crate::type_theory::commons::unification::{ucs, Substitution};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::{Kernel, Reducer};
use std::collections::VecDeque;

fn is_substitutable(term: &CicTerm) -> Option<String> {
    match term {
        Meta(idx) => Some(format!("metavariable_{}", idx)),
        Variable(var_name, _dbi) => {
            if !is_constant(term) {
                Some(format!("variable_{}", var_name))
            } else {
                None
            }
        }
        _ => None,
    }
}
fn structurally_equal(term1: &CicTerm, term2: &CicTerm) -> bool {
    match (term1, term2) {
        (Sort(_), Sort(_)) => true,
        (Meta(_), Meta(_)) => true,
        // TODO this is a bug: ? and Nat should be able to unify the same way x and 3 can at FO
        // however this needs to make sure the Variable actually is a type name and not some random term
        // idx == GLOBAL_INDEX is a current hack (global type names get assigned this value) but should be fixed
        (Meta(_), Variable(_, idx)) | (Variable(_, idx), Meta(_)) => {
            *idx == GLOBAL_INDEX
        }
        (Variable(name1, dbi1), Variable(name2, dbi2)) => {
            // same dbi1 and if they are global constants then also the constant symbols must be the same
            dbi1 == dbi2 && (!is_constant(term1) || name1 == name2)
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
fn occurs_meta_check(meta_index: i32, term: &CicTerm) -> Result<(), LofError> {
    match term {
        Meta(index) => {
            if meta_index == *index {
                Err(LofError::occurs_check_cyclic(format!(
                    "metavariable_{}",
                    meta_index
                )))
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
fn occurs_var_check(term: &CicTerm, name: &str) -> bool {
    match term {
        Sort(_) => false,
        Variable(var_name, _) => var_name == name,
        Abstraction(var_name, var_type, body) => {
            (var_name != name && occurs_var_check(var_type, name))
                || (var_name != name && occurs_var_check(body, name))
        }
        Product(var_name, var_type, body) => {
            (var_name != name && occurs_var_check(var_type, name))
                || (var_name != name && occurs_var_check(body, name))
        }
        Application(func, arg) => {
            occurs_var_check(func, name) || occurs_var_check(arg, name)
        }
        Match(scrutinee, branches) => {
            occurs_var_check(scrutinee, name)
                || branches.iter().any(|(pattern, body)| {
                    occurs_var_check(pattern, name)
                        || occurs_var_check(body, name)
                })
        }
        Let(var_name, var_type, value, body) => {
            let type_occurs = if let Some(ty) = var_type.as_ref() {
                occurs_var_check(ty, name)
            } else {
                false
            };
            (var_name != name && type_occurs)
                || (var_name != name && occurs_var_check(value, name))
                || (var_name != name && occurs_var_check(body, name))
        }
        Meta(_) => false,
    }
}
fn occurs(term: &CicTerm, name: &str) -> bool {
    if name.starts_with("metavariable_") {
        occurs_meta_check(
            name.strip_prefix("metavariable_").unwrap().parse().unwrap(),
            term,
        )
        .is_err()
    } else if name.starts_with("variable_") {
        occurs_var_check(term, name.strip_prefix("variable_").unwrap())
    } else {
        panic!("CIC occurs check is being called on a name that isnt formed by any of the 2 prefixes used. this shuold NOT happen");
    }
}

/// Binary second order unification of meta-variable for type inference
/// This function does NOT support normalization of terms to be unified and hence
/// does not require an environment to be passed
pub fn cic_so_unification(
    term1: &CicTerm,
    term2: &CicTerm,
) -> Result<Substitution<CicTerm>, LofError> {
    solve_unifications_unnormalized(VecDeque::from([(
        term1.to_owned(),
        term2.to_owned(),
    )]))
}

pub fn cic_solve_unifications(
    constraints: Vec<(CicTerm, CicTerm)>,
    environment: &mut Environment<Cic>,
) -> Result<Substitution<CicTerm>, LofError> {
    let mut reduced_constraints = VecDeque::new();
    for (left, right) in constraints {
        reduced_constraints.push_back((
            Cic::normalize_term(environment, &left),
            Cic::normalize_term(environment, &right),
        ));
        // reduced_constraints.push_back((left, right));
    }

    solve_unifications_unnormalized(reduced_constraints)
}

fn solve_unifications_unnormalized(
    constraints: VecDeque<(CicTerm, CicTerm)>,
) -> Result<Substitution<CicTerm>, LofError> {
    Ok(ucs(
        &mut Substitution::empty(),
        constraints,
        is_substitutable,
        structurally_equal,
        explode,
        occurs,
    )?
    .reduce(|term, idx, arg| {
        let stripped_idx = idx.strip_prefix("metavariable_").unwrap_or(idx);
        substitute_meta(term, &stripped_idx.parse().unwrap(), arg)
    }))
}

pub fn cic_collect_unifications(
    term: &CicTerm,
    environment: &mut Environment<Cic>,
) -> Result<Vec<(CicTerm, CicTerm)>, LofError> {
    match term {
        Abstraction(_var_name, var_type, body) => {
            let type_cons = cic_collect_unifications(var_type, environment)?;
            let body_cons = cic_collect_unifications(body, environment)?;

            Ok([type_cons, body_cons].concat())
        }
        Application(fun, arg) => {
            let fun_cons = cic_collect_unifications(fun, environment)?;
            let arg_cons = cic_collect_unifications(arg, environment)?;

            let arg_type = Cic::type_check_term(arg, environment)?;
            let fun_type = Cic::type_check_term(fun, environment)?;
            let first_arg_type = &get_arg_types(&fun_type)[0];

            Ok([
                fun_cons,
                vec![(first_arg_type.to_owned(), arg_type)],
                arg_cons,
            ]
            .concat())
        }
        _ => Ok(vec![]),
    }
}
pub fn cic_apply_unifier(
    exp: &CicTerm,
    substitution: &Substitution<CicTerm>,
) -> CicTerm {
    let mut solved_exp = exp.to_owned();
    for index in substitution.names() {
        solved_exp = substitute_meta(
            &solved_exp,
            &index
                .strip_prefix("metavariable_")
                .unwrap_or(index)
                .parse()
                .unwrap(),
            substitution.get(index).unwrap(),
        )
    }
    solved_exp
}

#[cfg(test)]
mod unit_tests {
    use crate::type_theory::cic::cic::{Cic, FIRST_INDEX};
    use crate::type_theory::cic::cic::{
        CicStm::{Fun, InductiveDef},
        CicTerm::{
            self, Abstraction, Application, Let, Match, Meta, Product, Sort,
            Variable,
        },
        GLOBAL_INDEX,
    };
    use crate::type_theory::cic::unification::{
        cic_so_unification, cic_solve_unifications, explode, is_substitutable,
        occurs, solve_unifications_unnormalized,
    };
    use crate::type_theory::commons::unification::Substitution;
    use crate::type_theory::interface::{Kernel, TypeTheory};
    use std::collections::VecDeque;

    #[test]
    fn test_variable_ground_unification() {
        fn var(name: &str) -> CicTerm {
            Variable(name.to_string(), -100)
        }
        let listbool =
            Application(Box::new(var("List")), Box::new(var("Bool")));
        let listt = Application(
            Box::new(var("List")),
            Box::new(Variable("T".to_string(), FIRST_INDEX)),
        );
        assert!(cic_so_unification(&listbool, &listt).is_ok(), "nook");
    }

    #[test]
    fn test_dhm() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        assert_eq!(
            cic_so_unification(&Meta(0), &nat).unwrap(),
            Substitution::from([("metavariable_0".to_string(), nat.clone())]),
            "Unification couldnt solve one simple constraint"
        );

        let constraints = vec![
            (
                Meta(1),
                Product(
                    "_".to_string(),
                    Box::new(nat.clone()),
                    Box::new(Meta(0)),
                ),
            ),
            (Meta(0), nat.clone()),
        ];
        let expected = Substitution::from([
            (
                "metavariable_1".to_string(),
                Product(
                    "_".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ),
            ),
            ("metavariable_0".to_string(), nat.clone()),
        ]);
        assert_eq!(
                cic_solve_unifications(constraints, &mut Cic::default_environment()).unwrap(),
                expected,
                "Unification couldnt solve a problem with a function over metavariables"
            );
    }

    #[test]
    fn test_match_unification() {
        let t = Variable("true".to_string(), GLOBAL_INDEX);
        let expected =
            Substitution::from([("metavariable_1".to_string(), t.clone())]);
        let constraints = vec![(
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
            solve_unifications_unnormalized(VecDeque::from(constraints)).unwrap(),
            expected,
            "Unification couldnt solve a problem of constructor recovery in pattern matching"
        );

        let body = Sort("TYPE".to_string());
        let expected =
            Substitution::from([("metavariable_2".to_string(), body.clone())]);
        let constraints = vec![(
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
            solve_unifications_unnormalized(VecDeque::from(constraints))
                .unwrap(),
            expected,
            "Unification couldnt solve unification of pattern match bodies"
        );
    }

    #[test]
    fn test_substitutability() {
        assert_eq!(
            is_substitutable(&Meta(420)),
            Some("metavariable_420".to_string()),
            "is_substitutable check doesnt return proper naming for a metavariable"
        );
        assert_eq!(
            is_substitutable(&Variable("super_idol".to_string(), 69)),
            Some("variable_super_idol".to_string()),
            "is_substitutable check doesnt return proper naming for a variable"
        );
        assert!(
            is_substitutable(&Sort("TYPE".to_string())).is_none(),
            "is_substitutable check returns a key for a term different from [meta]variables"
        );
        assert!(
            is_substitutable(&Application(Box::new(Variable("".to_string(), 0)), Box::new(Meta(0)))).is_none(),
            "is_substitutable check returns a key for a term different from [meta]variables"
        );
        assert!(
            is_substitutable(&Product("".to_string(), Box::new(Meta(0)), Box::new(Variable("".to_string(), 0)))).is_none(),
            "is_substitutable check returns a key for a term different from [meta]variables"
        );
        assert!(
            is_substitutable(&Abstraction("".to_string(), Box::new(Meta(0)), Box::new(Variable("".to_string(), 0)))).is_none(),
            "is_substitutable check returns a key for a term different from [meta]variables"
        );
        assert!(
            is_substitutable(&Match(
                Box::new(Variable("".to_string(), 0)),
                vec![
                    (Variable("".to_string(), 0), Meta(0))
                ]
            )).is_none(),
            "is_substitutable check returns a key for a term different from [meta]variables"
        );
        assert!(
            is_substitutable(&Let("".to_string(), Box::new(Some(Meta(0))), Box::new(Variable("".to_string(), 0)), Box::new(Sort("TYPE".to_string())))).is_none(),
            "is_substitutable check returns a key for a term different from [meta]variables"
        );
    }

    #[test]
    fn test_explosion() {
        let subterm1 = Sort("dope".to_string());
        let subterm2 = Sort("dope".to_string());
        assert_eq!(
            explode(&Sort("".to_string())),
            vec![],
            "CIC explosion doesnt produce the proper subcomponents vector"
        );
        assert_eq!(
            explode(&Meta(63)),
            vec![],
            "CIC explosion doesnt produce the proper subcomponents vector"
        );
        assert_eq!(
            explode(&Variable("".to_string(), 0)),
            vec![],
            "CIC explosion doesnt produce the proper subcomponents vector"
        );
        assert_eq!(
            explode(&Abstraction(
                "".to_string(),
                Box::new(subterm1.clone()),
                Box::new(subterm2.clone())
            )),
            vec![subterm1.clone(), subterm2.clone()],
            "CIC explosion doesnt produce the proper subcomponents vector"
        );
        assert_eq!(
            explode(&Product(
                "".to_string(),
                Box::new(subterm1.clone()),
                Box::new(subterm2.clone())
            )),
            vec![subterm1.clone(), subterm2.clone()],
            "CIC explosion doesnt produce the proper subcomponents vector"
        );
        assert_eq!(
            explode(&Application(
                Box::new(subterm1.clone()),
                Box::new(subterm2.clone())
            )),
            vec![subterm1.clone(), subterm2.clone()],
            "CIC explosion doesnt produce the proper subcomponents vector"
        );
        // TODO: test these too
        // assert_eq!(
        //     explode(&Match(subterm1.clone(), vec![(subterm2.clone(), ?)])),
        //     vec![],
        //     "CIC explosion doesnt produce the proper subcomponents vector"
        // );
        // assert_eq!(
        //     explode(&Let("".to_string())),
        //     vec![],
        //     "CIC explosion doesnt produce the proper subcomponents vector"
        // );
    }

    #[test]
    fn test_cic_occurs() {
        let variable = Variable("name".to_string(), 0);
        let name_key = "variable_name";
        let meta = Meta(16 * 29);
        let meta_key = &format!("metavariable_{}", 16 * 29);
        let random = Sort("TYPE".to_string());

        assert!(
            occurs(&variable, name_key),
            "occurs check doesnt see variable"
        );
        assert!(
            occurs(
                &Application(
                    Box::new(Variable("f".to_string(), GLOBAL_INDEX)),
                    Box::new(variable.clone())
                ),
                name_key
            ),
            "occurs check doesnt see variable"
        );
        assert!(
            occurs(
                &Let(
                    "".to_string(),
                    Box::new(None),
                    Box::new(Variable("exp".to_string(), 0)),
                    Box::new(variable.clone())
                ),
                name_key
            ),
            "occurs check doesnt see variable"
        );

        assert!(
            occurs(&meta, meta_key),
            "occurs check doesnt see metavariable"
        );
        assert!(
            occurs(
                &Abstraction(
                    "T".to_string(),
                    Box::new(meta.clone()),
                    Box::new(random.clone())
                ),
                meta_key
            ),
            "occurs check doesnt see metavariable"
        );
        assert!(
            occurs(
                &Application(
                    Box::new(Variable("nil".to_string(), GLOBAL_INDEX)),
                    Box::new(meta.clone())
                ),
                meta_key
            ),
            "occurs check doesnt see metavariable"
        );

        assert!(
            occurs(
                &Match(
                    Box::new(Variable("".to_string(), 42)),
                    vec![
                        (Variable("true".to_string(), 0), variable.clone()),
                        (Variable("false".to_string(), 0), meta.clone())
                    ]
                ),
                name_key
            ),
            "occurs check doesnt see variable"
        );
        assert!(
            occurs(
                &Match(
                    Box::new(Variable("".to_string(), 42)),
                    vec![
                        (Variable("true".to_string(), 0), variable.clone()),
                        (Variable("false".to_string(), 0), meta.clone())
                    ]
                ),
                meta_key
            ),
            "occurs check doesnt see metavariable"
        );
        assert!(
            !occurs(
                &Match(
                    Box::new(Variable("".to_string(), 42)),
                    vec![
                        (Variable("true".to_string(), 0), variable.clone()),
                        (Variable("false".to_string(), 0), meta.clone())
                    ]
                ),
                "variable_missing_key"
            ),
            "occurs passes on unreferenced variable"
        );
        assert!(
            !occurs(&Sort(name_key.to_string()), name_key),
            "occurs check passes on a sort which isnt a substitutable term"
        );
        assert!(
            !occurs(&Sort(format!("{}", meta_key)), meta_key),
            "occurs check passes on a sort which isnt a substitutable term"
        );
        assert!(
            !occurs(
                &Abstraction(
                    "T".to_string(),
                    Box::new(Sort("TYPE".to_string())),
                    Box::new(Sort("TYPE".to_string()))
                ),
                name_key
            ),
            "occurs check passes on a term that doesnt reference the variable"
        );
    }

    #[test]
    fn test_plus_zero_one_unification() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let mut env = Cic::default_environment();

        Cic::type_check_stm(
            &InductiveDef(
                "Nat".to_string(),
                vec![],
                Box::new(Sort("TYPE".to_string())),
                vec![
                    ("z".to_string(), nat.clone()),
                    (
                        "s".to_string(),
                        Product(
                            "_".to_string(),
                            Box::new(nat.clone()),
                            Box::new(nat.clone()),
                        ),
                    ),
                ],
            ),
            &mut env,
        )
        .expect("Failed to set up Nat");

        Cic::type_check_stm(
            &Fun(
                "plus".to_string(),
                vec![
                    ("n".to_string(), nat.clone()),
                    ("m".to_string(), nat.clone()),
                ],
                Box::new(nat.clone()),
                Box::new(Match(
                    Box::new(Variable("n".to_string(), GLOBAL_INDEX)),
                    vec![
                        (
                            Variable("z".to_string(), GLOBAL_INDEX),
                            Variable("m".to_string(), GLOBAL_INDEX),
                        ),
                        (
                            Application(
                                Box::new(Variable(
                                    "s".to_string(),
                                    GLOBAL_INDEX,
                                )),
                                Box::new(Variable(
                                    "nn".to_string(),
                                    GLOBAL_INDEX,
                                )),
                            ),
                            Application(
                                Box::new(Variable(
                                    "s".to_string(),
                                    GLOBAL_INDEX,
                                )),
                                Box::new(Application(
                                    Box::new(Application(
                                        Box::new(Variable(
                                            "plus".to_string(),
                                            GLOBAL_INDEX,
                                        )),
                                        Box::new(Variable(
                                            "nn".to_string(),
                                            GLOBAL_INDEX,
                                        )),
                                    )),
                                    Box::new(Variable(
                                        "m".to_string(),
                                        GLOBAL_INDEX,
                                    )),
                                )),
                            ),
                        ),
                    ],
                )),
                true,
            ),
            &mut env,
        )
        .expect("Failed to set up plus");

        let z = Variable("z".to_string(), GLOBAL_INDEX);
        let s = Variable("s".to_string(), GLOBAL_INDEX);
        let one = Application(Box::new(s.clone()), Box::new(z.clone()));
        let plus_zero_one = Application(
            Box::new(Application(
                Box::new(Variable("plus".to_string(), GLOBAL_INDEX)),
                Box::new(z.clone()),
            )),
            Box::new(one.clone()),
        );

        assert!(
            cic_solve_unifications(vec![(plus_zero_one, one)], &mut env)
                .is_ok(),
            // cic_unification(&mut env, &plus_zero_one, &one).is_ok(),
            "plus(z, s(z)) should unify with s(z) after normalization"
        );
    }
}
