use super::evaluation::{
    generic_evaluate_axiom, generic_evaluate_fun, generic_evaluate_let,
    generic_evaluate_theorem,
};
use crate::{
    misc::Union::{self, L, R},
    parser::api::Tactic,
    type_theory::{
        environment::Environment,
        interface::{Interactive, Kernel, Refiner, TypeTheory},
    },
};

//########################### EXPRESSIONS TYPE CHECKING
/// Generic variable type checking. Implements the classic VAR type checking
/// rule of checking x:T ∈ Γ, where x is `var_name`, T the returned type, and
/// Γ the `environment`
pub fn type_check_variable<T: TypeTheory>(
    environment: &mut Environment<T>,
    var_name: &str,
) -> Result<T::Type, String> {
    match environment.get_variable_type(var_name) {
        Some(var_type) => Ok(var_type),
        None => Err(format!("Unbound variable: {}", var_name)),
    }
}

/// Generic abstraction type checking. Implements classic ABS type checking
/// rule of Γ ⊢ λa:A.b : A->B, where a is `var_name`, A is `var_type`, b is
/// `body`, and B is the returned type.
/// This function does not support unification solving for implicit types
pub fn type_check_abstraction<
    T: TypeTheory + Kernel,
    C: Fn(String, T::Type, T::Type) -> T::Type,
>(
    environment: &mut Environment<T>,
    var_name: &str,
    var_type: &T::Type,
    body: &T::Term,
    constructor: C,
) -> Result<T::Type, String> {
    let _ = T::type_check_type(var_type, environment)?;
    environment.with_local_assumption(var_name, var_type, |local_env| {
        let body_type = T::type_check_term(body, local_env)?;
        Ok(constructor(
            var_name.to_string(),
            var_type.to_owned(),
            body_type,
        ))
    })
}

pub fn u_type_check_abstraction<
    T: TypeTheory + Kernel + Refiner,
    C: Fn(String, T::Type, T::Type) -> T::Type,
>(
    environment: &mut Environment<T>,
    var_name: &str,
    var_type: &T::Type,
    body: &T::Term,
    constructor: C,
) -> Result<T::Type, String> {
    let _ = T::type_check_type(var_type, environment)?;
    environment.with_local_assumption(var_name, var_type, |local_env| {
        let body_type = T::type_check_term(body, local_env)?;
        let meta_index = T::meta_index(&body_type);

        let (var_type, body_type) = if meta_index.is_some() {
            // let meta_index = meta_index.unwrap();
            let substitution =
                T::solve_unification(local_env.get_constraints())?;

            let simplified_arg_type = T::type_solve_metas(
                var_type,
                // &meta_index,
                // substitution.get(&meta_index).unwrap(),
                &substitution,
            );
            let simplified_body_type = T::type_solve_metas(
                &body_type,
                &substitution, // &meta_index,
                               // substitution.get(&meta_index).unwrap(),
            );

            (simplified_arg_type, simplified_body_type)
        } else {
            (var_type.to_owned(), body_type)
        };

        Ok(constructor(var_name.to_string(), var_type, body_type))
    })
}

/// Generic universal quantification type checking. Implements first order
/// universal quantification Γ ⊢ ∀a:A.P(a), where a is `var_name`, A is
/// `var_type`, and P(a) is a dependent `predicate`.
/// Creating the dependent type Πa:A.P a is left to type theories implementations
pub fn type_check_universal<T: TypeTheory + Kernel>(
    environment: &mut Environment<T>,
    var_name: &str,
    var_type: &T::Type,
    predicate: &T::Type,
) -> Result<T::Type, String> {
    let _ = T::type_check_type(var_type, environment)?;
    environment.with_local_assumption(var_name, var_type, |local_env| {
        let body_type = T::type_check_type(predicate, local_env)?;
        // TODO return the body type or the quantification itself via constructor?
        Ok(body_type)
    })
}

// pub fn type_check_application<T: TypeTheory>(
//     environment: &mut Environment<T>,
//     left: T::Term,
//     right: T::Term,
// ) -> Result<T::Type, String> {
//     fn type_check_nested_app<T: TypeTheory>(
//         local_env: &mut Environment<T>,
//         term: T::Term,
//     ) -> Result<T::Type, String> {
//         match term {
//             // idncutive case:
//             Application(left, right) => {
//                 let function_type =
//                     type_check_nested_app(local_env, *left.clone())?;
//                 let arg_type = T::type_check_term(*right.clone(), local_env)?;

//                 match function_type.clone() {
//                     T::Term::Function(var_name, domain, codomain) => {
//                         if T::base_type_equality(&domain, &arg_type) {
//                             local_env.add_variable_definition(&var_name, &right, &arg_type);
//                             // δ-reduce the body type in case its dependent on var_name
//                             match delta_reduce(local_env, *codomain.clone()) {
//                                 Ok(body) => Ok(body),
//                                 _ => Ok(*codomain)
//                             }
//                         } else {
//                             Err(format!(
//                                 "Function and argument have uncompatible types: function expects a {:?} but the argument has type {:?}",
//                                 *domain,
//                                 arg_type
//                             ))
//                         }
//                     }
//                     _ => Err(format!(
//                         "Attempted application on non functional term '{:?}' of type: {:?}",
//                         left,
//                         function_type
//                     )),
//                 }
//             }
//             // base case: type check the fuction (leftmost term)
//             _ => {
//                 let term_type = T::type_check_term(term, local_env)?;
//                 Ok(term_type)
//             }
//         }
//     }

//     environment.with_rollback(|local_env| {
//         type_check_nested_app(
//             local_env,
//             Application(Box::new(left), Box::new(right)),
//         )
//     })
// }
//########################### EXPRESSIONS TYPE CHECKING
//
//########################### STATEMENTS TYPE CHECKING
//
/// Generic let definition type checking. Uses `T::type_check_type` on the variable type
pub fn type_check_let<T: TypeTheory + Kernel>(
    environment: &mut Environment<T>,
    var_name: &str,
    opt_type: &Option<T::Type>,
    body: &T::Term,
) -> Result<T::Type, String> {
    let body_type = T::type_check_term(body, environment)?;
    let var_type = if opt_type.is_none() {
        body_type.to_owned()
    } else {
        opt_type.to_owned().unwrap()
    };
    let _ = T::type_check_type(&var_type, environment)?;

    if T::base_type_equality(&var_type, &body_type).is_ok() {
        generic_evaluate_let::<T>(environment, var_name, &Some(var_type), body);
        Ok(body_type)
    } else {
        Err(format!(
            "Error in variable {} definition: declared type {:?} and assigned {:?} do not unify",
            var_name,
            var_type,
            var_type
        ))
    }
}

/// Generic function definition type checking
pub fn type_check_function<
    T: TypeTheory + Kernel,
    C: Fn(Vec<(String, T::Type)>, T::Type) -> T::Type,
>(
    environment: &mut Environment<T>,
    fun_name: &str,
    args: &Vec<(String, T::Type)>,
    out_type: &T::Type,
    body: &T::Term,
    is_rec: &bool,
    constructor: C,
) -> Result<T::Type, String> {
    let fun_type = constructor(args.to_owned(), out_type.to_owned());
    let _ = T::type_check_type(&fun_type, environment);
    let mut assumptions = args.to_owned();
    if *is_rec {
        assumptions.push((fun_name.to_string(), fun_type.clone()));
        //TODO possibly include necessary checks on recursive functions
    }

    let body_type = environment
        .with_local_assumptions(&assumptions, |local_env| {
            T::type_check_term(&body, local_env)
        })?;
    if T::base_type_equality(out_type, &body_type).is_err() {
        return Err(format!(
            "In {} definition, function type {:?} and body result {:?} are inconsistent",
            fun_name, out_type, body_type
        ));
    }

    generic_evaluate_fun::<T, _>(
        environment,
        fun_name,
        args,
        out_type,
        body,
        is_rec,
        constructor,
    );
    Ok(fun_type)
}

/// Generic axiom type checking. Uses `T::type_check_type` on `predicate` and
/// updates the environment with the axiom
pub fn type_check_axiom<T: TypeTheory + Kernel>(
    environment: &mut Environment<T>,
    axiom_name: &str,
    predicate: &T::Type,
) -> Result<T::Type, String> {
    let _ = T::type_check_type(predicate, environment)?;
    generic_evaluate_axiom::<T>(environment, axiom_name, predicate);

    Ok(predicate.to_owned())
}

/// Generic theorem type checking. If `proof` is a term style proof it type checks
/// the body and checks unification with the theorem `formula`;
pub fn type_check_theorem<T: TypeTheory + Kernel + Interactive>(
    environment: &mut Environment<T>,
    theorem_name: &str,
    formula: &T::Type,
    proof: &Union<T::Term, Vec<Tactic<T::Exp>>>,
) -> Result<T::Type, String> {
    let _ = T::type_check_type(formula, environment)?;
    match proof {
        L(proof_term) => {
            let proof_type = T::type_check_term(proof_term, environment)?;
            if T::base_type_equality(&formula, &proof_type).is_err() {
                return Err(format!(
                    "Proof term's type doesn't unify with the theorem statement. Expected {:?} but found {:?}",
                    formula, proof_type
                ));
            }
            generic_evaluate_theorem::<T, T::Exp>(
                environment,
                theorem_name,
                formula,
                proof,
            );
        }
        R(interactive_proof) => {
            let (target, proof) = type_check_interactive_proof::<T>(
                environment,
                interactive_proof,
                formula,
                &T::proof_hole(),
            )?;
            // check that the proof proves the statement
            if target == T::empty_target() {
                let proof_type = T::type_check_term(&proof, environment)?;
                if T::base_type_equality(&proof_type, formula).is_err() {
                    return Err(format!(
                        "Theorem checking failed. Proof has type {:?} while stated type is {:?}",
                        proof_type, formula
                    ));
                }
            }
        }
    }
    Ok(formula.to_owned())
}

fn type_check_interactive_proof<T: TypeTheory + Interactive>(
    environment: &mut Environment<T>,
    interactive_proof: &[Tactic<T::Exp>],
    target: &T::Type,
    partial_proof: &T::Term,
) -> Result<(T::Type, T::Term), String> {
    match interactive_proof {
        [] => Ok((target.to_owned(), partial_proof.to_owned())),
        [proof_step, rest @ ..] => {
            // type_check_tactic(proof_step)
            let (new_target, new_proof) = T::type_check_tactic(
                environment,
                proof_step,
                &target,
                &partial_proof,
            )?;
            // TODO update target and context
            // run recursively on rest
            type_check_interactive_proof::<T>(
                environment,
                rest,
                &new_target,
                &new_proof,
            )
        }
    }
}
//########################### STATEMENTS TYPE CHECKING
