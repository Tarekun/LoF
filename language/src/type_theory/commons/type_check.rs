use crate::{
    error::LofError,
    misc::Union::{self, L, R},
    parser::api::Tactic,
    type_theory::{
        commons::evaluation::{
            evaluate_axiom, evaluate_fun, evaluate_global, evaluate_theorem,
        },
        environment::Environment,
        interface::{Interactive, Kernel, Reducer, Refiner, TypeTheory},
    },
};

//########################### EXPRESSIONS TYPE CHECKING
/// Generic variable type checking. Implements the classic VAR type checking
/// rule of checking x:T ∈ Γ, where x is `var_name`, T the returned type, and
/// Γ the `environment`
pub fn type_check_variable<T: TypeTheory>(
    environment: &mut Environment<T>,
    var_name: &str,
) -> Result<T::Type, LofError> {
    match environment.get_variable_type(var_name) {
        Some(var_type) => Ok(var_type),
        None => Err(LofError::unbound_variable(var_name)),
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
) -> Result<T::Type, LofError> {
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

/// Generic abstraction type checking. Implements classic ABS type checking
/// rule of Γ ⊢ λa:A.b : A->B, where a is `var_name`, A is `var_type`, b is
/// `body`, and B is the returned type.
/// This function does support inference and requires implementation of `Refiner`
pub fn i_type_check_abstraction<
    T: TypeTheory + Kernel + Refiner,
    C: Fn(String, T::Type, T::Type) -> T::Type,
>(
    environment: &mut Environment<T>,
    var_name: &str,
    var_type: &T::Type,
    body: &T::Term,
    constructor: C,
) -> Result<T::Type, LofError> {
    let _ = T::type_check_type(var_type, environment)?;
    environment.with_local_assumption(var_name, var_type, |local_env| {
        let body_type = T::type_check_term(body, local_env)?;
        let type_cons = T::type_collect_unifications(var_type, local_env)?;
        let body_cons = T::term_collect_unifications(body, local_env)?;
        let constraints = [type_cons, body_cons].concat();
        let substitution = T::solve_unifications(constraints, local_env)?;

        let var_type = T::type_apply_unifier(var_type, &substitution);
        let body_type = T::type_apply_unifier(&body_type, &substitution);

        Ok(constructor(var_name.to_string(), var_type, body_type))
    })
}

/// Generic application type checking. Implements classic APP type checking
/// rule of Γ ⊢ f x : T of unary function application.
/// This function does not support unification solving for implicit types
/// and does not support functions with dependent types
pub fn type_check_application<
    T: TypeTheory + Kernel,
    F: Fn(&T::Type) -> Option<(T::Type, T::Type)>,
>(
    environment: &mut Environment<T>,
    left: &T::Term,
    right: &T::Term,
    unpack_fun_type: F,
) -> Result<T::Type, LofError> {
    let arg_type = T::type_check_term(right, environment)?;
    let function_type = T::type_check_term(left, environment)?;

    if let Some((domain, codomain)) = unpack_fun_type(&function_type) {
        if T::base_type_equality(&domain, &arg_type).is_ok() {
            Ok(codomain)
        } else {
            Err(LofError::type_mismatch(
                "function application",
                &domain,
                &arg_type,
            ))
        }
    } else {
        Err(LofError::custom(format!(
            "Attempted application on non functional term of type: {:?}",
            function_type
        )))
    }
}

/// Generic application type checking. Implements classic APP type checking
/// rule of Γ ⊢ f x : T of unary function application.
/// This function does supports both unification-based type inference solving implicit
/// types and functions with term-dependent types
pub fn i_type_check_application<
    T: TypeTheory + Kernel + Refiner + Reducer,
    F: Fn(&T::Type) -> Option<(String, T::Type, T::Type)>,
    R: Fn(&T::Term, &T::Term) -> T::Term,
    S: Fn(&T::Type, &str, &T::Term) -> T::Type,
    E: Fn(&T::Type) -> T::Exp,
>(
    environment: &mut Environment<T>,
    left: &T::Term,
    right: &T::Term,
    unpack_fun_type: F,
    repack_application: R,
    substitute_type: S,
    type_as_expression: E,
) -> Result<T::Type, LofError> {
    let _arg_type = T::type_check_term(right, environment)?;
    let function_type = T::type_check_term(left, environment)?;
    // A function type read straight off an earlier application arrives as
    // an un-reduced substituted codomain - a dependent eliminator's result
    // is literally `motive(target, proof)`. Normalizing on the fallback
    // path keeps the fast case (an explicit Pi) free while still letting
    // such a term be applied.
    let function_type = match unpack_fun_type(&function_type) {
        Some(_) => function_type,
        None => T::normalize_type(environment, &function_type),
    };

    if let Some((var_name, domain, codomain)) = unpack_fun_type(&function_type)
    {
        // Only this node's own constraint - the argument's type against the
        // domain. Collecting over the whole `left right` term instead (as
        // this did) re-walks the entire function spine, and constraint
        // collection on an application itself type checks that
        // application's function: the two are mutually recursive, so the
        // cost doubles per argument. A six-argument curried application
        // nested three deep cost tens of millions of type-check calls.
        //
        // Nothing is lost: `left` and `right` were each just type checked
        // above, which collects and solves their own inner constraints.
        let constraints = vec![(
            type_as_expression(&domain),
            type_as_expression(&_arg_type),
        )];
        let substitution = T::solve_unifications(constraints, environment)?;
        let _ = &repack_application;

        let codomain = substitute_type(&codomain, &var_name, right);
        let codomain = T::type_apply_unifier(&codomain, &substitution);
        Ok(codomain)
    } else {
        Err(LofError::custom(format!(
            "Attempted application on non functional term of type: {:?}",
            function_type
        )))
    }
}

/// Generic universal quantification type checking. Implements first order
/// universal quantification Γ ⊢ ∀a:A.P(a), where a is `var_name`, A is
/// `var_type`, and P(a) is a term-dependent `predicate`.
/// Creating the dependent type Πa:A.P a is left to type theories implementations
pub fn type_check_fo_universal<T: TypeTheory + Kernel>(
    environment: &mut Environment<T>,
    var_name: &str,
    var_type: &T::Type,
    predicate: &T::Type,
) -> Result<T::Type, LofError> {
    let _ = T::type_check_type(var_type, environment)?;
    environment.with_local_assumption(var_name, var_type, |local_env| {
        let body_type = T::type_check_type(predicate, local_env)?;
        // TODO return the body type or the quantification itself via constructor?
        Ok(body_type)
    })
}

/// Generic let definition type checking
pub fn type_check_let<T: TypeTheory + Kernel>(
    environment: &mut Environment<T>,
    var_name: &str,
    var_type: &Option<T::Type>,
    body: &T::Term,
    scope: &T::Term,
) -> Result<T::Type, LofError> {
    let body_type = T::type_check_term(body, environment)?;
    let var_type = if var_type.is_none() {
        body_type.to_owned()
    } else {
        var_type.to_owned().unwrap()
    };

    if T::base_type_equality(&var_type, &body_type).is_ok() {
        Ok(environment.with_local_substitution(
            var_name,
            body,
            &Some(var_type),
            // type of a let is the type of the scope term as it reduces to that
            |local_env| T::type_check_term(scope, local_env),
        )?)
    } else {
        Err(LofError::type_mismatch(
            format!("let binding `{}`", var_name),
            &var_type,
            &body_type,
        ))
    }
}

//########################### EXPRESSIONS TYPE CHECKING
//
//########################### STATEMENTS TYPE CHECKING
//
/// Generic global definition type checking. Uses `T::type_check_type` on the variable type
pub fn type_check_global<T: TypeTheory + Kernel>(
    environment: &mut Environment<T>,
    var_name: &str,
    opt_type: &Option<T::Type>,
    body: &T::Term,
) -> Result<T::Type, LofError> {
    let body_type = T::type_check_term(body, environment)?;
    let var_type = if opt_type.is_none() {
        body_type.to_owned()
    } else {
        opt_type.to_owned().unwrap()
    };
    let _ = T::type_check_type(&var_type, environment)?;

    if T::base_type_equality(&var_type, &body_type).is_ok() {
        let _ =
            evaluate_global::<T>(environment, var_name, &Some(var_type), body);
        Ok(body_type)
    } else {
        Err(LofError::type_mismatch(
            format!("global `{}`", var_name),
            &var_type,
            &body_type,
        ))
    }
}

/// Generic function definition type checking
pub fn type_check_function<
    T: TypeTheory + Kernel,
    C: Fn(Vec<(String, T::Type)>, T::Type) -> T::Type,
    E: Fn((String, T::Type), T::Term) -> T::Term,
>(
    environment: &mut Environment<T>,
    fun_name: &str,
    args: &Vec<(String, T::Type)>,
    out_type: &T::Type,
    body: &T::Term,
    is_rec: &bool,
    constructor: C,
    eta_wrap: E,
) -> Result<T::Type, LofError> {
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
        return Err(LofError::type_mismatch(
            format!("function `{}`", fun_name),
            out_type,
            &body_type,
        ));
    }

    // include fun_namefun_name into the context for following script
    let _ = evaluate_fun::<T, _, _>(
        environment,
        fun_name,
        args,
        out_type,
        body,
        is_rec,
        |args, out_type| constructor(args.to_owned(), out_type.to_owned()),
        eta_wrap,
    );
    Ok(fun_type)
}

/// Generic axiom type checking. Uses `T::type_check_type` on `predicate` and
/// updates the environment with the axiom
pub fn type_check_axiom<T: TypeTheory + Kernel>(
    environment: &mut Environment<T>,
    axiom_name: &str,
    predicate: &T::Type,
) -> Result<T::Type, LofError> {
    let _ = T::type_check_type(predicate, environment)?;
    let _ = evaluate_axiom::<T>(environment, axiom_name, predicate);

    Ok(predicate.to_owned())
}

/// Generic equality-based theorem type checking, supporting both term-based and
/// tactic-based proofs.
/// This variants uses type equality to compare the inhabited type against the
/// target one (ie T::base_type_equality)
pub fn eq_type_check_theorem<T: TypeTheory + Kernel + Interactive>(
    environment: &mut Environment<T>,
    theorem_name: &str,
    formula: &T::Type,
    proof: &Union<T::Term, Vec<Tactic<T::Exp>>>,
) -> Result<T::Type, LofError> {
    type_check_theorem_base(
        environment,
        theorem_name,
        formula,
        proof,
        |proof_type, formula, _| {
            T::base_type_equality(proof_type, formula).is_ok()
        },
    )
}
/// Generic unification-based theorem type checking, supporting both term-based
/// and tactic-based proofs.
/// This variants uses type unification to compare the inhabited type against the
/// target one (ie T::types_unify)
pub fn u_type_check_theorem<T: TypeTheory + Kernel + Interactive + Refiner>(
    environment: &mut Environment<T>,
    theorem_name: &str,
    formula: &T::Type,
    proof: &Union<T::Term, Vec<Tactic<T::Exp>>>,
) -> Result<T::Type, LofError> {
    type_check_theorem_base(
        environment,
        theorem_name,
        formula,
        proof,
        |proof_type, formula, environment| {
            T::types_unify(environment, proof_type, formula).is_ok()
        },
    )
}
/// Base implementation for generic type checking of theorem proofs, parametric
/// on `are_compatible` for types (equality, unification).
/// Includes `theorem_name` in the context for future usage
fn type_check_theorem_base<
    T: TypeTheory + Kernel + Interactive,
    P: FnMut(&T::Type, &T::Type, &mut Environment<T>) -> bool,
>(
    environment: &mut Environment<T>,
    theorem_name: &str,
    formula: &T::Type,
    proof: &Union<T::Term, Vec<Tactic<T::Exp>>>,
    mut are_compatible: P,
) -> Result<T::Type, LofError> {
    let _ = T::type_check_type(formula, environment)?;
    match proof {
        L(proof_term) => {
            let proof_type = T::type_check_term(proof_term, environment)?;
            if !are_compatible(&proof_type, formula, environment) {
                return Err(LofError::type_mismatch(
                    "proof checking of proven statement and target",
                    formula,
                    &proof_type,
                ));
            }
            // Record the proof term for later introspection (eg by
            // `transport`) - theorems otherwise behave like axioms
            // (opaque for reduction), so without this their witness term
            // is unrecoverable once checked.
            environment.add_theorem_proof(theorem_name, proof_term);
        }
        R(interactive_proof) => {
            let proof = type_check_interactive_proof::<T>(
                environment,
                interactive_proof,
                formula,
            )?;
            // check that the proof proves the statement
            let proof_type = T::type_check_term(&proof, environment)?;
            if !are_compatible(&proof_type, formula, environment) {
                // TODO figure out what to do in this branch:
                // this is a pratial proof are we sure we should fail if the goal isnt matched?
                // proof_type might not be syntactically equal to formula but unify with it; should it fail or require refinement?

                // return Err(format!(
                //         "Theorem checking failed. Proof has type {:?} while stated type is {:?}",
                //         proof_type, formula
                //     ));
            }
            environment.add_theorem_proof(theorem_name, &proof);
        }
    }
    // include theorem_name into the context for following script, for both
    // term-mode and tactic-mode proofs
    let _ = evaluate_theorem::<T, T::Exp>(
        environment,
        theorem_name,
        formula,
        proof,
    );

    Ok(formula.to_owned())
}

/// Generic auto command type checking. It checks that the target formula is well formed
pub fn type_check_auto<T: TypeTheory + Kernel>(
    environment: &mut Environment<T>,
    formula: &T::Type,
) -> Result<T::Type, LofError> {
    let _ = T::type_check_type(formula, environment)?;
    Ok(formula.to_owned())
}

fn type_check_interactive_proof<T: TypeTheory + Interactive>(
    environment: &mut Environment<T>,
    interactive_proof: &[Tactic<T::Exp>],
    target: &T::Type,
) -> Result<T::Term, LofError> {
    fn solver<T: TypeTheory + Interactive>(
        environment: &mut Environment<T>,
        interactive_proof: &[Tactic<T::Exp>],
        mut subgoals: Vec<T::Type>,
        partial_proof: T::Term,
    ) -> Result<T::Term, LofError> {
        // TODO: make sure the proof closes with a qed.
        if subgoals.is_empty() {
            return Ok(partial_proof.to_owned());
        }

        match interactive_proof {
            [] => Ok(partial_proof.to_owned()),
            [proof_step, rest @ ..] => {
                let target = subgoals.pop().unwrap();
                let (new_proof, new_subgoals) = T::type_check_tactic(
                    environment,
                    proof_step,
                    &target,
                    &partial_proof,
                )?;
                subgoals.extend(new_subgoals);

                solver::<T>(environment, rest, subgoals, new_proof)
            }
        }
    }

    // rollback to avoid env contamination with changes possibly made by tactics
    environment.with_rollback(|local_env| {
        solver(
            local_env,
            interactive_proof,
            vec![target.to_owned()],
            T::proof_hole(),
        )
    })
}
//########################### STATEMENTS TYPE CHECKING

#[cfg(test)]
#[path = "../../tests/type_theory/commons/type_check.rs"]
mod tests;
