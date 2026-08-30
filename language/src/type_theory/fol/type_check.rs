use super::fol::FolFormula::{
    Arrow, Conjunction, Disjunction, ForAll, Not, Predicate,
};
use super::fol::{
    Fol, FolFormula,
    FolTerm::{self, Abstraction},
};
use super::fol_utils::make_multiarg_fun_type;
use crate::error::LofError;
use crate::type_theory::commons::type_check::{
    type_check_fo_universal, type_check_function,
};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::{Kernel, TypeTheory};

//########################### TERMS TYPE CHECKING
pub fn type_check_tuple(
    environment: &mut Environment<Fol>,
    terms: &Vec<FolTerm>,
) -> Result<FolFormula, LofError> {
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
) -> Result<FolFormula, LofError> {
    match environment.get_predicate(pred_name) {
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
                            return Err(LofError::type_mismatch(
                                format!("predicate `{}` application", pred_name),
                                formal_type,
                                &actual_type,
                            ));
                        }
                    }
                    // note: this also covers (None, None) which shouldnt be possible
                    // TODO should i make it explicit and put an unreachable! ?
                    (_, _) => {
                        return Err(LofError::arity_mismatch(
                            format!("predicate `{}`", pred_name),
                            arg_types.len(),
                            args.len(),
                        ));
                    }
                }
            }

            Ok(Predicate(pred_name.to_string(), args.to_owned()))
        }
        // fall back to the context for predicates declared via axiom
        None => {
            // TODO this fallback logic should be implemented somewhere in the Environment type, not here
            if environment.get_variable_type(pred_name).is_some() {
                Ok(Predicate(pred_name.to_string(), args.to_owned()))
            } else {
                Err(LofError::unbound_predicate(pred_name))
            }
        }
    }
}
//
//
pub fn type_check_arrow(
    environment: &mut Environment<Fol>,
    domain: &FolFormula,
    codomain: &FolFormula,
) -> Result<FolFormula, LofError> {
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
) -> Result<FolFormula, LofError> {
    let _body_type = type_check_fo_universal::<Fol>(
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
) -> Result<FolFormula, LofError> {
    let φ = Fol::type_check_type(φ, environment)?;
    Ok(Not(Box::new(φ)))
}
//
//
pub fn type_check_conjunction(
    environment: &mut Environment<Fol>,
    sub_formulas: &Vec<FolFormula>,
) -> Result<FolFormula, LofError> {
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
) -> Result<FolFormula, LofError> {
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
) -> Result<FolFormula, LofError> {
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

#[cfg(test)]
#[path = "../../tests/type_theory/fol/type_check.rs"]
mod tests;
