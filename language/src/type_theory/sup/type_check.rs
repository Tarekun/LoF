use super::{
    sup::Sup,
    sup_utils::{get_arg_types, get_forall_innermost},
};
use crate::type_theory::{
    commons::type_check::type_check_variable,
    environment::Environment,
    grammars::cnf::{
        CnfFormula::{self, Atom, Clause, Equality, ForAll, Not},
        CnfTerm,
    },
    interface::TypeTheory,
};
use crate::{
    error::LofError,
    misc::simple_map,
    type_theory::{
        commons::type_check::type_check_fo_universal, interface::Kernel,
    },
};

//########################### TERMS TYPE CHECKING
pub fn type_check_application(
    environment: &mut Environment<Sup>,
    fun_name: &str,
    args: &Vec<CnfTerm>,
) -> Result<CnfFormula, LofError> {
    type_check_nary(environment, fun_name, args)?;
    let (_, fun_type) = environment.get_from_context(fun_name).unwrap();
    // Sup shouldnt have dependent types
    Ok(get_forall_innermost(&fun_type))
}
//########################### TERMS TYPE CHECKING
//
//########################### TYPES TYPE CHECKING
pub fn type_check_atomic(
    environment: &mut Environment<Sup>,
    pred_name: &str,
    args: &Vec<CnfTerm>,
) -> Result<CnfFormula, LofError> {
    type_check_nary(environment, pred_name, args)?;
    Ok(Atom(pred_name.to_string(), args.clone()))
}
//
//
pub fn type_check_equality(
    env: &mut Environment<Sup>,
    t1: &CnfTerm,
    t2: &CnfTerm,
) -> Result<CnfFormula, LofError> {
    Sup::term_judgemental_equality(env, t1, t2)?;
    Ok(Equality(t1.clone(), t2.clone()))
}
//
//
pub fn type_check_not(
    environment: &mut Environment<Sup>,
    ψ: &CnfFormula,
) -> Result<CnfFormula, LofError> {
    Sup::type_check_type(ψ, environment)?;
    Ok(Not(Box::new(ψ.clone())))
}
//
//
pub fn type_check_forall(
    environment: &mut Environment<Sup>,
    var_name: &str,
    var_type: &CnfFormula,
    ψ: &CnfFormula,
) -> Result<CnfFormula, LofError> {
    let _ = type_check_fo_universal::<Sup>(environment, var_name, var_type, ψ)?;

    Ok(ForAll(
        var_name.to_string(),
        Box::new(var_type.to_owned()),
        Box::new(ψ.to_owned()),
    ))
}
//
//
pub fn type_check_clause(
    environment: &mut Environment<Sup>,
    literals: &Vec<CnfFormula>,
) -> Result<CnfFormula, LofError> {
    fn is_literal(formula: &CnfFormula) -> bool {
        match formula {
            Atom(_, _) => true,
            Not(p) => match **p {
                Atom(_, _) => true,
                _ => false,
            },
            _ => false,
        }
    }

    for lit in literals {
        if is_literal(lit) {
            let _ = Sup::type_check_type(lit, environment)?;
        } else {
            return Err(LofError::type_mismatch("clause", &"a literal", lit));
        }
    }

    Ok(Clause(literals.clone()))
}

//########################### TYPES TYPE CHECKING
//
//########################### HELPER FUNCTIONS
fn type_check_nary(
    environment: &mut Environment<Sup>,
    applied: &str,
    args: &Vec<CnfTerm>,
) -> Result<(), LofError> {
    let applied_type = type_check_variable::<Sup>(environment, applied)?;

    // check actual arguments are well typed
    let actual_types_res =
        simple_map(args.clone(), |arg| Sup::type_check_term(&arg, environment));
    let mut actual_types = vec![];
    let mut errors = vec![];
    for type_res in actual_types_res {
        match type_res {
            Err(err) => errors.push(err),
            Ok(typee) => actual_types.push(typee),
        }
    }
    if !errors.is_empty() {
        return Err(LofError::aggregate(errors));
    }

    // check actual arguments match formals
    let formal_types = get_arg_types(&applied_type);
    if formal_types.len() != actual_types.len() {
        return Err(LofError::arity_mismatch(
            format!("predicate `{}`", applied),
            formal_types.len(),
            actual_types.len(),
        ));
    }
    for i in 0..formal_types.len() {
        if Sup::type_judgemental_equality(
            environment,
            &formal_types[i],
            &actual_types[i],
        )
        .is_err()
        {
            return Err(LofError::type_mismatch(
                format!("predicate `{}` argument", applied),
                &formal_types[i],
                &actual_types[i],
            ));
        }
    }

    Ok(())
}
//########################### HELPER FUNCTIONS

#[cfg(test)]
#[path = "../../tests/type_theory/sup/type_check.rs"]
mod tests;
