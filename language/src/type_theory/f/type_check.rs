use super::f::{SystemF, TYPE_KIND};
use crate::error::LofError;
use crate::type_theory::commons::type_check::type_check_variable as generic_type_check_variable;
use crate::type_theory::environment::Environment;
use crate::type_theory::grammars::{
    f::{
        FTerm,
        FType::{self, Arrow, Atomic, Forall},
    },
    traits::NamedSubstitution,
};
use crate::type_theory::interface::Kernel;

/// Returns the kind `*` of proper types
pub fn kind() -> FType {
    Atomic(TYPE_KIND.to_string())
}

fn is_kind(typee: &FType) -> bool {
    matches!(typee, Atomic(name) if name == TYPE_KIND)
}

/// Kinds other than `*` would need type operators, ie System Fω
fn check_kind(kind: &FType) -> Result<(), LofError> {
    if is_kind(kind) {
        Ok(())
    } else {
        Err(LofError::unsupported(format!(
            "Kind {:?} is not supported, System F only has the kind {}",
            kind, TYPE_KIND
        )))
    }
}

/// Checks that `typee` is a proper type, ie a well formed type of kind `*`
fn check_proper_type(
    typee: &FType,
    environment: &mut Environment<SystemF>,
) -> Result<(), LofError> {
    if is_kind(typee) {
        return Err(LofError::custom(format!(
            "Expected a type, found the kind {}",
            TYPE_KIND
        )));
    }
    SystemF::type_check_type(typee, environment).map(|_| ())
}

//########################### TERMS TYPE CHECKING
pub fn type_check_variable(
    environment: &mut Environment<SystemF>,
    var_name: &str,
) -> Result<FType, LofError> {
    let var_type =
        generic_type_check_variable::<SystemF>(environment, var_name)?;
    if is_kind(&var_type) {
        Err(LofError::custom(format!(
            "`{}` is a type, not a term",
            var_name
        )))
    } else {
        Ok(var_type)
    }
}
//
//
pub fn type_check_abstraction(
    environment: &mut Environment<SystemF>,
    var_name: &str,
    var_type: &FType,
    body: &FTerm,
) -> Result<FType, LofError> {
    check_proper_type(var_type, environment)?;
    let body_type =
        environment.with_local_assumption(var_name, var_type, |local_env| {
            SystemF::type_check_term(body, local_env)
        })?;

    Ok(Arrow(Box::new(var_type.to_owned()), Box::new(body_type)))
}
//
//
pub fn type_check_type_abstraction(
    environment: &mut Environment<SystemF>,
    var_name: &str,
    kind: &FType,
    body: &FTerm,
) -> Result<FType, LofError> {
    check_kind(kind)?;
    let body_type =
        environment.with_local_assumption(var_name, kind, |local_env| {
            SystemF::type_check_term(body, local_env)
        })?;

    Ok(Forall(
        var_name.to_string(),
        Box::new(kind.to_owned()),
        Box::new(body_type),
    ))
}
//
//
pub fn type_check_type_application(
    environment: &mut Environment<SystemF>,
    fun: &FTerm,
    type_arg: &FType,
) -> Result<FType, LofError> {
    let fun_type = SystemF::type_check_term(fun, environment)?;
    let Forall(var_name, _, body) = fun_type else {
        return Err(LofError::custom(format!(
            "Attempted type application on non polymorphic term of type: {:?}",
            fun_type
        )));
    };
    // the kind was already checked to be `*` on the Forall's formation
    check_proper_type(type_arg, environment)?;

    Ok(body.substitute_name(&var_name, type_arg))
}
//########################### TERMS TYPE CHECKING
//
//
//########################### TYPES TYPE CHECKING
pub fn type_check_atomic(
    environment: &mut Environment<SystemF>,
    type_name: &str,
) -> Result<FType, LofError> {
    // the kind itself is accepted, so that base types can be declared as `name: *`
    if type_name == TYPE_KIND {
        return Ok(kind());
    }

    match environment.get_variable_type(type_name) {
        Some(var_kind) if is_kind(&var_kind) => Ok(var_kind),
        Some(var_type) => Err(LofError::custom(format!(
            "`{}` is a term of type {:?}, not a type",
            type_name, var_type
        ))),
        None => Err(LofError::UnboundName {
            kind: "type",
            name: type_name.to_string(),
        }),
    }
}
//
//
pub fn type_check_arrow(
    environment: &mut Environment<SystemF>,
    domain: &FType,
    codomain: &FType,
) -> Result<FType, LofError> {
    check_proper_type(domain, environment)?;
    check_proper_type(codomain, environment)?;
    Ok(kind())
}
//
//
pub fn type_check_forall(
    environment: &mut Environment<SystemF>,
    var_name: &str,
    var_kind: &FType,
    body: &FType,
) -> Result<FType, LofError> {
    check_kind(var_kind)?;
    environment.with_local_assumption(var_name, var_kind, |local_env| {
        check_proper_type(body, local_env)
    })?;
    Ok(kind())
}
//########################### TYPES TYPE CHECKING

#[cfg(test)]
#[path = "../../tests/type_theory/f/type_check.rs"]
mod tests;
