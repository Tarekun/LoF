use super::{
    sup::{
        Sup,
        SupFormula::{self, Atom, Clause, Equality, ForAll, Not},
        SupTerm,
    },
    sup_utils::{get_arg_types, get_forall_innermost},
};
use crate::type_theory::{
    commons::type_check::type_check_variable, environment::Environment,
    interface::TypeTheory,
};
use crate::{
    misc::simple_map,
    type_theory::{
        commons::type_check::type_check_universal, interface::Kernel,
    },
};

//########################### TERMS TYPE CHECKING
pub fn type_check_application(
    environment: &mut Environment<Sup>,
    fun_name: &str,
    args: &Vec<SupTerm>,
) -> Result<SupFormula, String> {
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
    args: &Vec<SupTerm>,
) -> Result<SupFormula, String> {
    type_check_nary(environment, pred_name, args)?;
    Ok(Atom(pred_name.to_string(), args.clone()))
}
//
//
pub fn type_check_equality(
    _: &mut Environment<Sup>,
    t1: &SupTerm,
    t2: &SupTerm,
) -> Result<SupFormula, String> {
    Sup::base_term_equality(t1, t2)?;
    Ok(Equality(t1.clone(), t2.clone()))
}
//
//
pub fn type_check_not(
    environment: &mut Environment<Sup>,
    ψ: &SupFormula,
) -> Result<SupFormula, String> {
    Sup::type_check_type(ψ, environment)?;
    Ok(Not(Box::new(ψ.clone())))
}
//
//
pub fn type_check_forall(
    environment: &mut Environment<Sup>,
    var_name: &str,
    var_type: &SupFormula,
    ψ: &SupFormula,
) -> Result<SupFormula, String> {
    let _ = type_check_universal::<Sup>(environment, var_name, var_type, ψ)?;

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
    literals: &Vec<SupFormula>,
) -> Result<SupFormula, String> {
    fn is_literal(formula: &SupFormula) -> bool {
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
            return Err(format!(
                "Clauses can only contain literals, not {:?}",
                lit
            ));
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
    args: &Vec<SupTerm>,
) -> Result<(), String> {
    let applied_type = type_check_variable::<Sup>(environment, applied)?;

    // check actual arguments are well typed
    let actual_types_res =
        simple_map(args.clone(), |arg| Sup::type_check_term(&arg, environment));
    let mut actual_types = vec![];
    let mut errors = vec![];
    for type_res in actual_types_res {
        match type_res {
            Err(message) => errors.push(message),
            Ok(typee) => actual_types.push(typee),
        }
    }
    if !errors.is_empty() {
        return Err(format!(
            "Predicate application {} failed with:\n{}",
            applied,
            errors.join("\n")
        ));
    }

    // check actual arguments match formals
    let formal_types = get_arg_types(&applied_type);
    if formal_types.len() != actual_types.len() {
        return Err(format!(
            "Predicate {} expects {} arguments, but {} were given",
            applied,
            formal_types.len(),
            actual_types.len()
        ));
    }
    for i in 0..formal_types.len() {
        if Sup::base_type_equality(&formal_types[i], &actual_types[i]).is_ok() {
            return Err(format!(
                "Missmatched types, {} expects a {:?}, but {:?} was found",
                applied, formal_types[i], actual_types[i]
            ));
        }
    }

    Ok(())
}
//########################### HELPER FUNCTIONS
