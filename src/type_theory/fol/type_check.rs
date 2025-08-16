use super::fol::FolFormula::{
    Arrow, Conjunction, Disjunction, ForAll, Not, Predicate,
};
use super::fol::{
    Fol, FolFormula,
    FolTerm::{self, Abstraction},
};
use super::fol_utils::make_multiarg_fun_type;
use crate::type_theory::commons::type_check::{
    type_check_function, type_check_universal,
};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::{Kernel, TypeTheory};

//########################### TERMS TYPE CHECKING
pub fn type_check_application(
    environment: &mut Environment<Fol>,
    left: &FolTerm,
    right: &FolTerm,
) -> Result<FolFormula, String> {
    let function_type = Fol::type_check_term(left, environment)?;
    let arg_type = Fol::type_check_term(right, environment)?;

    match function_type {
        Arrow(domain, codomain) => {
            if Fol::base_type_equality(&(*domain), &arg_type).is_ok() {
                Ok(*codomain)
            } else {
                Err(format!(
                    "Function and argument have uncompatible types: function expects a {:?} but the argument has type {:?}", 
                    *domain,
                    arg_type
                ))
            }
        }
        _ => Err(format!(
            "Attempted application on non functional term of type: {:?}",
            function_type
        )),
    }
}
//
//
pub fn type_check_tuple(
    environment: &mut Environment<Fol>,
    terms: &Vec<FolTerm>,
) -> Result<FolFormula, String> {
    let mut types = vec![];
    for term in terms {
        let term_type = Fol::type_check_term(term, environment)?;
        types.push(term_type);
    }

    Ok(Conjunction(types))
}
//########################### TERMS TYPE CHECKING
//
//
//########################### TYPES TYPE CHECKING
pub fn type_check_predicate(
    environment: &mut Environment<Fol>,
    pred_name: &str,
    args: &Vec<FolTerm>,
) -> Result<FolFormula, String> {
    match environment.get_predicate(pred_name) {
        None => Err(format!("Unbound predicate {}", pred_name)),
        Some(arg_types) => {
            for i in 0..arg_types.len().max(args.len()) {
                let formal_type = arg_types.get(i);
                let actual_type = if args.get(i).is_none() {
                    None
                } else {
                    Some(Fol::type_check_term(&args[i], environment)?)
                };

                match (formal_type, actual_type) {
                    (Some(formal_type), Some(actual_type)) => {
                        if let Err(_msg) =
                            Fol::base_type_equality(&actual_type, &arg_types[i])
                        {
                            return Err(format!(
                                "Predicate application type doesn't match the argument; expected {:?} found {:?}.",
                                formal_type, actual_type
                            ));
                        }
                    }
                    // note: this also covers (None, None) which shouldnt be possible
                    // TODO should i make it explicit and put an unreachable! ?
                    (_, _) => {
                        return Err(format!(
                            "Predicate application argument missmatch; {} expects {} arguments, but {} were given",
                            pred_name, arg_types.len(), args.len()
                        ));
                    }
                }
            }

            Ok(Predicate(pred_name.to_string(), args.to_owned()))
        }
    }
}
//
//
pub fn type_check_arrow(
    environment: &mut Environment<Fol>,
    domain: &FolFormula,
    codomain: &FolFormula,
) -> Result<FolFormula, String> {
    let _ = Fol::type_check_type(domain, environment)?;
    let _ = Fol::type_check_type(codomain, environment)?;

    Ok(Arrow(
        Box::new(domain.to_owned()),
        Box::new(codomain.to_owned()),
    ))
}
//
//
pub fn type_check_forall(
    environment: &mut Environment<Fol>,
    var_name: &str,
    var_type: &FolFormula,
    predicate: &FolFormula,
) -> Result<FolFormula, String> {
    let _body_type = type_check_universal::<Fol>(
        environment,
        var_name,
        var_type,
        predicate,
    )?;
    Ok(ForAll(
        var_name.to_string(),
        Box::new(var_type.to_owned()),
        Box::new(predicate.to_owned()),
    ))
}
//
//
pub fn type_check_not(
    environment: &mut Environment<Fol>,
    φ: &FolFormula,
) -> Result<FolFormula, String> {
    let φ = Fol::type_check_type(φ, environment)?;
    Ok(Not(Box::new(φ)))
}
//
//
pub fn type_check_conjunction(
    environment: &mut Environment<Fol>,
    sub_formulas: &Vec<FolFormula>,
) -> Result<FolFormula, String> {
    for φ in sub_formulas {
        Fol::type_check_type(φ, environment)?;
    }
    Ok(Conjunction(sub_formulas.to_owned()))
}
//
//
pub fn type_check_disjunction(
    environment: &mut Environment<Fol>,
    sub_formulas: &Vec<FolFormula>,
) -> Result<FolFormula, String> {
    // equal to the conjuction one; this checks well formedness of the type
    // not correctes of a proof for φ ∨ ψ
    for φ in sub_formulas {
        Fol::type_check_type(φ, environment)?;
    }
    Ok(Disjunction(sub_formulas.to_owned()))
}
//########################### TYPES TYPE CHECKING
//
//########################### STATEMENTS TYPE CHECKING
pub fn fol_type_check_fun(
    environment: &mut Environment<Fol>,
    fun_name: &str,
    args: &Vec<(String, FolFormula)>,
    out_type: &FolFormula,
    body: &FolTerm,
    is_rec: &bool,
) -> Result<FolFormula, String> {
    type_check_function::<Fol, _, _>(
        environment,
        fun_name,
        args,
        out_type,
        body,
        is_rec,
        |args, body_type| make_multiarg_fun_type(&args, &body_type),
        |(var_name, var_type), body| {
            Abstraction(var_name, Box::new(var_type), Box::new(body))
        },
    )
}
//
//########################### STATEMENTS TYPE CHECKING

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::type_theory::{
        environment::Environment,
        fol::{
            fol::{
                Fol,
                FolFormula::{self, Arrow, ForAll, Predicate},
                FolStm::{Axiom, Fun, Let},
                FolTerm::{Abstraction, Application, Variable},
            },
            type_check::{
                type_check_application, type_check_arrow, type_check_forall,
                type_check_predicate,
            },
        },
        interface::{Kernel, TypeTheory},
    };

    #[test]
    fn test_var_type_check() {
        let mut test_env = Fol::default_environment();
        test_env.add_to_context("it", &Predicate("Unit".to_string(), vec![]));

        assert_eq!(
            Fol::type_check_term(&Variable("it".to_string()), &mut test_env),
            Ok(Predicate("Unit".to_string(), vec![])),
            "Variable type checking isnt working properly"
        );
        assert!(
            Fol::type_check_term(
                &Variable("stupid_unbound_variable".to_string()),
                &mut test_env,
            )
            .is_err(),
            "Variable type checking is accepting unbound variable"
        );
        assert!(
            Fol::type_check_term(&Variable("it".to_string()), &mut test_env,)
                .is_ok(),
            "Top level type checker doesnt support variables"
        );
    }

    #[test]
    fn test_abs_type_check() {
        let mut test_env = Fol::default_environment();
        let unit = Predicate("Unit".to_string(), vec![]);

        assert_eq!(
            Fol::type_check_term(
                &Abstraction(
                    "x".to_string(),
                    Box::new(unit.clone()),
                    Box::new(Variable("x".to_string()))
                ),
                &mut test_env,
            ),
            Ok(Arrow(Box::new(unit.clone()), Box::new(unit.clone()))),
            "Abstraction type checker doesnt work properly"
        );
        assert!(
            Fol::type_check_term(
                &Abstraction(
                    "x".to_string(),
                    Box::new(unit.clone()),
                    Box::new(Variable("x".to_string())),
                ),
                &mut test_env,
            )
            .is_ok(),
            "Top level type checking doesnt support abstraction"
        );

        assert!(
            Fol::type_check_term(
                &Abstraction(
                    "x".to_string(),
                    Box::new(Predicate(
                        "StupidUnboundType".to_string(),
                        vec![]
                    )),
                    Box::new(Variable("x".to_string()))
                ),
                &mut test_env,
            )
            .is_err(),
            "Abstraction type checker accepts argument over undefined type"
        );
        assert!(
            Fol::type_check_term(
                &Abstraction(
                    "x".to_string(),
                    Box::new(Predicate(
                        "StupidUnboundType".to_string(),
                        vec![]
                    )),
                    Box::new(Variable("stupid_unbound_variable".to_string()))
                ),
                &mut test_env,
            )
            .is_err(),
            "Abstraction type checker accepts argument over ill typed body"
        );
    }

    #[test]
    fn test_app_type_check() {
        let unit = Predicate("Unit".to_string(), vec![]);
        let nat = Predicate("Nat".to_string(), vec![]);
        let mut test_env: Environment<Fol> = Environment::with_defaults(
            vec![],
            vec![],
            vec![("Nat", &vec![]), ("Unit", &vec![])],
        );
        test_env.add_to_context(
            "f",
            &Arrow(Box::new(nat.clone()), Box::new(nat.clone())),
        );
        test_env.add_to_context("x", &nat.clone());
        test_env.add_to_context("it", &unit.clone());

        assert_eq!(
            type_check_application(
                &mut test_env,
                &Variable("f".to_string()),
                &Variable("x".to_string())
            ),
            Ok(nat.clone()),
            "Application type checker doesnt work properly"
        );
        assert!(
            Fol::type_check_term(
                &Application(
                    Box::new(Variable("f".to_string())),
                    Box::new(Variable("x".to_string()))
                ),
                &mut test_env,
            )
            .is_ok(),
            "Top level type checking doesnt support application"
        );

        assert!(
            type_check_application(
                &mut test_env,
                &Variable("stupid_unbound_fun".to_string()),
                &Variable("x".to_string())
            )
            .is_err(),
            "Application type checking accepts unbound function"
        );
        assert!(
            type_check_application(
                &mut test_env,
                &Variable("f".to_string()),
                &Variable("stupid_unbound_arg".to_string())
            )
            .is_err(),
            "Application type checking accepts unbound argument"
        );
        assert!(
            type_check_application(
                &mut test_env,
                &Variable("f".to_string()),
                &Variable("it".to_string())
            )
            .is_err(),
            "Application type checking accepts application with incompatible types"
        );
    }

    #[test]
    fn test_sort_type_check() {
        let unit = Predicate("Unit".to_string(), vec![]);
        let mut test_env: Environment<Fol> =
            Environment::with_defaults(vec![], vec![], vec![("Unit", &vec![])]);

        assert!(
            type_check_predicate(&mut test_env, "Unit", &vec![]).is_ok(),
            "Predicate-type type checking refutes bound type"
        );
        assert!(
            Fol::type_check_type(&unit.clone(), &mut test_env).is_ok(),
            "Top level type checker doesnt support Predicate types"
        );
        assert!(
            type_check_predicate(&mut test_env, "StupidUnboundType", &vec![])
                .is_err(),
            "Predicate-type type checking accepts unbound type"
        );
    }

    #[test]
    fn test_arrow_type_check() {
        let nat = Predicate("Nat".to_string(), vec![]);
        let mut test_env: Environment<Fol> =
            Environment::with_defaults(vec![], vec![], vec![("Nat", &vec![])]);

        assert!(
            type_check_arrow(&mut test_env, &nat, &nat).is_ok(),
            "Arrow type checker refutes simple Nat->Nat"
        );
        assert!(
            Fol::type_check_type(
                &Arrow(Box::new(nat.clone()), Box::new(nat.clone())),
                &mut test_env
            )
            .is_ok(),
            "Top level type checker doesnt support arrow types"
        );
        assert!(
            type_check_arrow(
                &mut test_env,
                &Predicate("StupidUnboundType".to_string(), vec![]),
                &nat
            )
            .is_err(),
            "Arrow type checker accepts unbound domain"
        );
        assert!(
            type_check_arrow(
                &mut test_env,
                &nat,
                &Predicate("StupidUnboundType".to_string(), vec![]),
            )
            .is_err(),
            "Arrow type checker accepts unbound codomain"
        );
    }

    #[test]
    fn test_forall_type_check() {
        let top: FolFormula = Predicate("Top".to_string(), vec![]);
        let nat = Predicate("Nat".to_string(), vec![]);
        let mut test_env: Environment<Fol> = Environment::with_defaults(
            vec![],
            vec![],
            vec![("Top", &vec![]), ("Nat", &vec![])],
        );

        assert!(
            type_check_forall(&mut test_env, "x", &nat, &top).is_ok(),
            "Forall type checker doesnt work properly"
        );
        assert!(
            Fol::type_check_type(
                &ForAll(
                    "x".to_string(),
                    Box::new(nat.clone()),
                    Box::new(top.clone())
                ),
                &mut test_env,
            )
            .is_ok(),
            "Top level type checker doesnt support forall"
        );
        assert!(
            type_check_forall(
                &mut test_env,
                "x",
                &Predicate("StupidUnboundType".to_string(), vec![]),
                &top
            )
            .is_err(),
            "Forall type checker accepts forall dependent on unbound type"
        );
        assert!(
            type_check_forall(
                &mut test_env,
                "x",
                &nat,
                &Predicate("StupidUnboundType".to_string(), vec![]),
            )
            .is_err(),
            "Forall type checker accepts forall with ill typed body"
        );
    }

    #[test]
    fn test_axiom_type_check() {
        let top: FolFormula = Predicate("Top".to_string(), vec![]);
        let mut test_env: Environment<Fol> =
            Environment::with_defaults(vec![], vec![], vec![("Top", &vec![])]);
        let res = Fol::type_check_stm(
            &Axiom("test_axiom".to_string(), top.clone()),
            &mut test_env,
        );

        assert!(
            res.is_ok(),
            "Axiom type checker failed with error {:?}",
            res.err()
        );
        assert!(
            Fol::type_check_stm(
                &Axiom("other_name".to_string(), top.clone()),
                &mut test_env
            )
            .is_ok(),
            "Top level type checker doesnt support axioms",
        );
        assert_eq!(
            test_env.get_from_context("test_axiom"),
            Some(("test_axiom".to_string(), top)),
            "Axiom type checker did not update the context"
        );
    }

    #[test]
    fn test_let_type_check() {
        let nat = Predicate("Nat".to_string(), vec![]);
        let zero = Variable("zero".to_string());
        let mut test_env: Environment<Fol> = Environment::with_defaults(
            vec![("zero", &nat)],
            vec![],
            vec![("Nat", &vec![])],
        );

        let res = Fol::type_check_stm(
            &Let("n".to_string(), Some(nat.clone()), Box::new(zero.clone())),
            &mut test_env,
        );
        assert!(res.is_ok(), "Let type checker failed with {:?}", res.err());
        assert_eq!(
            test_env.get_from_deltas("n"),
            Some(("n".to_string(), zero.clone())),
            "Let type checker didnt update the context properly"
        );
        assert!(
            Fol::type_check_stm(
                &Let(
                    "m".to_string(),
                    Some(nat.clone()),
                    Box::new(zero.clone())
                ),
                &mut test_env
            )
            .is_ok(),
            "Top level type checker doesnt support let definitions"
        );
        assert!(
            Fol::type_check_stm(
                &Let("asd".to_string(), None, Box::new(zero.clone())),
                &mut test_env,
            )
            .is_ok(),
            "Let type checker refutes definition without type specified"
        );

        assert!(
            Fol::type_check_stm(
                &Let(
                    "o".to_string(),
                    Some(Predicate("StupidUnboundType".to_string(), vec![])),
                    Box::new(zero)
                ),
                &mut test_env,
            )
            .is_err(),
            "Let type checker accepts definition with declared unbound type"
        );
        assert!(
            Fol::type_check_stm(
                &Let(
                    "o".to_string(),
                    Some(nat.clone()),
                    Box::new(Variable("stupid_unbound_var".to_string()))
                ),
                &mut test_env,
            )
            .is_err(),
            "Let type checker accepts definition with ill typed body"
        );
    }

    #[test]
    fn test_fun_type_check() {
        let nat = Predicate("Nat".to_string(), vec![]);
        // let zero = Variable("zero".to_string());
        let mut test_env: Environment<Fol> =
            Environment::with_defaults(vec![], vec![], vec![("Nat", &vec![])]);

        let res = Fol::type_check_stm(
            &Fun(
                "f".to_string(),
                vec![("n".to_string(), nat.clone())],
                Box::new(nat.clone()),
                Box::new(Variable("n".to_string())),
                false,
            ),
            &mut test_env,
        );
        assert!(res.is_ok(), "Fun type checker failed with {:?}", res.err());
        assert_eq!(
            test_env.get_variable_type("f"),
            Some(Arrow(Box::new(nat.clone()), Box::new(nat.clone()))),
            "Fun type checker didnt update the context properly"
        );
        assert!(
            Fol::type_check_stm(
                &Fun(
                    "g".to_string(),
                    vec![("n".to_string(), nat.clone())],
                    Box::new(nat.clone()),
                    Box::new(Variable("n".to_string())),
                    false
                ),
                &mut test_env
            )
            .is_ok(),
            "Top level type checker doesnt support function definitions"
        );

        assert!(
            Fol::type_check_stm(
                &Fun(
                    "h".to_string(),
                    vec![("n".to_string(), Predicate("StupidUnboundName".to_string(), vec![]))],
                    Box::new(nat.clone()),
                    Box::new(Variable("n".to_string())),
                    false
                ),
                &mut test_env,
            ).is_err(),
            "Fun type checker accpets function definition with variable of unbound type"
        );
        assert!(
            Fol::type_check_stm(
                &Fun(
                    "h".to_string(),
                    vec![("n".to_string(), nat.clone())],
                    Box::new(nat.clone()),
                    Box::new(Variable("stupid_unbound_var".to_string())),
                    false
                ),
                &mut test_env,
            )
            .is_err(),
            "Fun type checker accpets function definition with ill typed body"
        );
        assert!(
            Fol::type_check_stm(
                &Fun(
                    "h".to_string(),
                    vec![("n".to_string(), nat.clone())],
                    Box::new(nat),
                    Box::new(Application(
                        Box::new(Variable("h".to_string())),
                        Box::new(Variable("n".to_string()))
                    )),
                    false
                ),
                &mut test_env,
            ).is_err(),
            "Fun type checker accpets normal function definition with recursive call"
        );
    }
}
