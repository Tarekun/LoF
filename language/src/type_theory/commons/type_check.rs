use crate::{
    error::LofError,
    misc::Union::{self, L, R},
    parser::api::Tactic,
    type_theory::{
        commons::evaluation::{
            evaluate_axiom, evaluate_fun, evaluate_global, evaluate_theorem,
        },
        environment::Environment,
        grammars::traits::LocallyNameless,
        interface::{Kernel, TypeTheory},
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

/// Generic abstraction type checking for systems that carry De Bruijn indices.
/// Implements classic ABS type checking rule of Γ ⊢ λa:A.b : Πa:A.B, where a
/// is `var_name`, A is `var_type`, b is `body`, and B is the type of the body.
/// The body is opened before being checked and its type closed back when
/// building the resulting product
pub fn ln_type_check_abstraction<
    T: TypeTheory + Kernel,
    C: Fn(String, T::Type, T::Type) -> T::Type,
>(
    environment: &mut Environment<T>,
    var_name: &str,
    var_type: &T::Type,
    body: &T::Term,
    constructor: C,
) -> Result<T::Type, LofError>
where
    T::Term: LocallyNameless,
    T::Type: LocallyNameless,
{
    let _ = T::type_check_type(var_type, environment)?;
    // opening var_name to a free variable inside body
    let opened_body = body.open(var_name);
    environment.with_local_assumption(var_name, var_type, |local_env| {
        let body_type = T::type_check_term(&opened_body, local_env)?;

        Ok(constructor(
            var_name.to_string(),
            var_type.to_owned(),
            body_type.close(var_name),
        ))
    })
}

/// `type_check_fo_universal` for systems that carry De Bruijn indices: the
/// quantified body is opened so its references to the bound variable stop
/// depending on the depth they are read at. Nothing is closed afterwards
/// because what comes back is the body's sort, which binds nothing.
pub fn ln_type_check_fo_universal<T: TypeTheory + Kernel>(
    environment: &mut Environment<T>,
    var_name: &str,
    var_type: &T::Type,
    predicate: &T::Type,
) -> Result<T::Type, LofError>
where
    T::Type: LocallyNameless,
{
    let _ = T::type_check_type(var_type, environment)?;
    // opening var_name to a free variable inside predicate
    let opened_predicate = predicate.open(var_name);
    environment.with_local_assumption(var_name, var_type, |local_env| {
        T::type_check_type(&opened_predicate, local_env)
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
        if T::type_judgemental_equality(environment, &domain, &arg_type).is_ok()
        {
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

/// Generic application type checking. Implements the dependent APP type
/// checking rule: Γ ⊢ f : Πx:A.B, Γ ⊢ a : A' and A' ≡ A imply Γ ⊢ f a : B[x := a].
/// `normalize_type` is used to expose the product type of `left` and the
/// argument type is compared using `T::type_judgemental_equality` (no inference)
pub fn ln_type_check_application<
    T: TypeTheory + Kernel,
    F: Fn(&T::Type) -> Option<(String, T::Type, T::Type)>,
    N: Fn(&Environment<T>, &T::Type) -> T::Type,
    S: Fn(&T::Type, &str, &T::Term) -> T::Type,
>(
    environment: &mut Environment<T>,
    left: &T::Term,
    right: &T::Term,
    unpack_fun_type: F,
    normalize_type: N,
    substitute_type: S,
) -> Result<T::Type, LofError> {
    let function_type = T::type_check_term(left, environment)?;
    let function_type = normalize_type(environment, &function_type);
    let arg_type = T::type_check_term(right, environment)?;

    if let Some((var_name, domain, codomain)) = unpack_fun_type(&function_type)
    {
        T::type_judgemental_equality(environment, &domain, &arg_type).map_err(|_| {
            LofError::type_mismatch("function application", &domain, &arg_type)
        })?;
        Ok(substitute_type(&codomain, &var_name, right))
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

    if T::type_judgemental_equality(environment, &var_type, &body_type).is_ok()
    {
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
/// Generic let definition type checking for systems that carry De Bruijn
/// indices: the scope is opened and checked with the definition in context.
/// `substitute_local` replaces the (now locally free) defined variable with
/// its definition in the resulting type, which would otherwise escape its scope
pub fn ln_type_check_let<
    T: TypeTheory + Kernel,
    S: Fn(&T::Type, &str, &T::Term) -> T::Type,
>(
    environment: &mut Environment<T>,
    var_name: &str,
    var_type: &Option<T::Type>,
    body: &T::Term,
    scope: &T::Term,
    substitute_local: S,
) -> Result<T::Type, LofError>
where
    T::Term: LocallyNameless,
{
    let body_type = T::type_check_term(body, environment)?;
    let var_type = match var_type {
        None => body_type.to_owned(),
        Some(var_type) => {
            let _ = T::type_check_type(var_type, environment)?;
            T::type_judgemental_equality(environment, var_type, &body_type).map_err(
                |_| {
                    LofError::type_mismatch(
                        format!("let binding `{}`", var_name),
                        var_type,
                        &body_type,
                    )
                },
            )?;
            var_type.to_owned()
        }
    };

    let opened_scope = scope.open(var_name);
    let scope_type = environment.with_local_substitution(
        var_name,
        body,
        &Some(var_type),
        // type of a let is the type of the scope term as it reduces to that
        |local_env| T::type_check_term(&opened_scope, local_env),
    )?;
    Ok(substitute_local(&scope_type, var_name, body))
}

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

    if T::type_judgemental_equality(environment, &var_type, &body_type).is_ok() {
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
    let _ = T::type_check_type(&fun_type, environment)?;
    let mut assumptions = args.to_owned();
    if *is_rec {
        assumptions.push((fun_name.to_string(), fun_type.clone()));
        //TODO possibly include necessary checks on recursive functions
    }

    let body_type = environment
        .with_local_assumptions(&assumptions, |local_env| {
            T::type_check_term(&body, local_env)
        })?;
    if T::type_judgemental_equality(environment, out_type, &body_type).is_err() {
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

/// `type_check_function` for systems that carry De Bruijn indices.
///
/// An argument's type is stated under the arguments preceding it, and the
/// return type and body under all of them, but none of those binders are
/// present in the terms themselves. Their references are therefore naked
/// indices, only meaningful at the depth they were elaborated at, so putting
/// them in the context as they are hands them back wrong at any other depth.
/// Opening the argument telescope first replaces them with `Local`s, which
/// carry no depth at all. What gets stored in the environment afterwards is
/// the original closed form, since that is what the rest of the program sees.
pub fn ln_type_check_function<
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
) -> Result<T::Type, LofError>
where
    T::Term: LocallyNameless,
    T::Type: LocallyNameless,
{
    let fun_type = constructor(args.to_owned(), out_type.to_owned());
    let _ = T::type_check_type(&fun_type, environment)?;

    // args contains a bunch of bound args that need to be opened both in subsequent args
    // and in the body and return type of the function
    let mut assumptions: Vec<(String, T::Type)> = vec![];
    for (arg_name, arg_type) in args {
        let opened_type = assumptions
            .iter()
            .rev()
            .fold(arg_type.to_owned(), |opened, (earlier_arg, _)| {
                opened.open(earlier_arg)
            });
        assumptions.push((arg_name.to_owned(), opened_type));
    }
    let opened_out_type = args
        .iter()
        .rev()
        .fold(out_type.to_owned(), |opened, (arg_name, _)| {
            opened.open(arg_name)
        });
    let opened_body = args
        .iter()
        .rev()
        .fold(body.to_owned(), |opened, (arg_name, _)| {
            opened.open(arg_name)
        });

    if *is_rec {
        // the recursive reference is not one of the binders the body was
        // elaborated under, so it is added closed and does not open anything
        assumptions.push((fun_name.to_string(), fun_type.clone()));
        //TODO possibly include necessary checks on recursive functions
    }

    let body_type = environment
        .with_local_assumptions(&assumptions, |local_env| {
            T::type_check_term(&opened_body, local_env)
        })?;
    if T::type_judgemental_equality(environment, &opened_out_type, &body_type).is_err() {
        return Err(LofError::type_mismatch(
            format!("function `{}`", fun_name),
            &opened_out_type,
            &body_type,
        ));
    }

    // include fun_name into the context for following script
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

/// Generic theorem type checking. Only proof terms are accepted: tactic
/// proofs are run by the (untrusted) `Refiner` into proof terms beforehand.
/// The type inhabited by the proof has to be convertible with the stated
/// `formula` (ie `T::type_judgemental_equality`).
/// Includes `theorem_name` in the context for future usage
pub fn type_check_theorem<T: TypeTheory + Kernel>(
    environment: &mut Environment<T>,
    theorem_name: &str,
    formula: &T::Type,
    proof: &Union<T::Term, Vec<Tactic<T::Term, T::Type>>>,
) -> Result<T::Type, LofError> {
    let _ = T::type_check_type(formula, environment)?;
    match proof {
        L(proof_term) => {
            let proof_type = T::type_check_term(proof_term, environment)?;
            if T::type_judgemental_equality(environment, formula, &proof_type).is_err()
            {
                return Err(LofError::type_mismatch(
                    format!("proof checking of theorem `{}`", theorem_name),
                    formula,
                    &proof_type,
                ));
            }
        }
        R(_) => {
            return Err(LofError::custom(format!(
                "Theorem `{}` reached the kernel with an unrefined tactic proof: tactics have to be run by the refiner into a proof term first",
                theorem_name
            )));
        }
    }
    // include theorem_name into the context for following script
    let _ = evaluate_theorem::<T>(
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

//########################### STATEMENTS TYPE CHECKING

#[cfg(test)]
#[path = "../../tests/type_theory/commons/type_check.rs"]
mod tests;
