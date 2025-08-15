use crate::{
    misc::Union,
    parser::api::Tactic,
    type_theory::{
        environment::Environment,
        interface::{Kernel, TypeTheory},
    },
};

/// Computes the normal form of `term` by iteratively calling `one_step_reduction`
/// on its result.
pub fn generic_term_normalization<
    T: TypeTheory,
    F: Fn(&mut Environment<T>, &T::Term) -> T::Term,
>(
    environment: &mut Environment<T>,
    term: &T::Term,
    one_step_reduction: F,
) -> T::Term {
    let mut reduced = one_step_reduction(environment, &term);
    while reduced != one_step_reduction(environment, &reduced) {
        reduced = one_step_reduction(environment, &reduced);
    }
    reduced
}

//########################### TERM βδ-REDUCTION
pub fn generic_reduce_variable<T: TypeTheory>(
    environment: &Environment<T>,
    var_name: &str,
    og_term: &T::Term,
) -> T::Term {
    // if a substitution exists the variable δ-reduces to its definition
    if let Some((_, body)) = environment.get_from_deltas(var_name) {
        body.to_owned()
    }
    // otherwise it's a constant, ie a value
    else {
        og_term.to_owned()
    }
}
//########################### TERM βδ-REDUCTION

//########################### STATEMENTS EXECUTION
pub fn generic_evaluate_let<T: TypeTheory + Kernel>(
    environment: &mut Environment<T>,
    var_name: &str,
    var_type: &Option<T::Type>,
    body: &T::Term,
) -> () {
    let var_type: &T::Type = match var_type {
        Some(type_term) => type_term,
        None => {
            let body_type = T::type_check_term(&body, environment);
            if body_type.is_err() {
                panic!("Evaluating a let definition with ill type body, this should have been caught sooner");
            }
            &body_type.unwrap()
        }
    };
    environment.add_substitution_with_type(var_name, body, var_type);
}
//
//
pub fn generic_evaluate_fun<
    T: TypeTheory,
    C: Fn(Vec<(String, T::Type)>, T::Type) -> T::Type,
>(
    environment: &mut Environment<T>,
    fun_name: &str,
    args: &Vec<(String, T::Type)>,
    out_type: &T::Type,
    body: &T::Term,
    _is_rec: &bool,
    constructor: C,
) -> () {
    let fun_type = constructor(args.to_owned(), out_type.to_owned());
    // TODO η-expand body cuz this aint it yungblood
    // let full_body = eta_expand(args, body);
    // let body = T::eta_expand(body, ...) type shi
    environment.add_substitution_with_type(fun_name, body, &fun_type);
}
//
//
pub fn generic_evaluate_axiom<T: TypeTheory>(
    environment: &mut Environment<T>,
    axiom_name: &str,
    formula: &T::Type,
) -> () {
    environment.add_to_context(axiom_name, formula);
}
//
//
pub fn generic_evaluate_theorem<T: TypeTheory, E>(
    environment: &mut Environment<T>,
    theorem_name: &str,
    formula: &T::Type,
    _proof: &Union<T::Term, Vec<Tactic<E>>>,
) -> () {
    environment.add_to_context(&theorem_name, &formula);
}
//########################### STATEMENTS EXECUTION
