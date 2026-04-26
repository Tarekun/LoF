use crate::{
    config::SelectionFunction,
    misc::Union,
    parser::api::Tactic,
    type_theory::{
        commons::{unification::Substitution, utils::eta_expand},
        environment::Environment,
        interface::{Automatic, Kernel, Reducer, TypeTheory},
        sup::{
            freedom::{get_selection_fn, pick_clause},
            saturation::saturate,
            sup::{Sup, SupFormula, SupTerm},
        },
    },
};

/// Computes the normal form of `term` by iteratively calling `one_step_reduction`
/// on its result.
/// Returns the transitive closure of ->β
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
/// Performs δ-reduction of a variable by looking it up in the `environment`.
/// If `var_name` is absent in the `environment` it's treated as a constant
/// and `og_term` is returned
pub fn reduce_variable<T: TypeTheory>(
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

/// Performs β-reduction of an unary application.<br>
/// First the `fun` term is reduced, then the `arg` is reduced.
/// Then if `unpack_name_body(fun)` returns the tuple (name, body),
/// `body` is returned where the name is substituted with `arg`,
/// otherwise it treats it like a constant and rebuilds the application
pub fn reduce_application<
    T: TypeTheory + Reducer,
    F: Fn(&T::Term) -> Option<(String, T::Term)>,
    G: Fn(T::Term, T::Term) -> T::Term,
>(
    environment: &mut Environment<T>,
    fun: &T::Term,
    arg: &T::Term,
    unpack_name_body: F,
    rebuild_application: G,
) -> T::Term {
    // if fun is function variable take its definition, otherwise gets fun back
    let fun_reduced = T::normalize_term(environment, fun);
    // TODO do i substitute arg or do i substitute its reduction? big deal
    let arg_reduced = T::normalize_term(environment, arg);

    match unpack_name_body(&fun_reduced) {
        Some((var_name, body)) => T::substitute(&body, &var_name, &arg_reduced),
        None => rebuild_application(fun.to_owned(), arg.to_owned()),
    }
}

/// Performs reduction of let definition where the definition term
/// is reduced to its scope term where `var_name` is substituted with
/// the `body`'s normal form
pub fn reduce_let<T: TypeTheory + Reducer>(
    environment: &mut Environment<T>,
    var_name: &str,
    _var_type: &Option<T::Type>,
    body: &T::Term,
    scope: &T::Term,
) -> T::Term {
    let body_reduced = T::normalize_term(environment, body);
    T::substitute(scope, var_name, &body_reduced)
}
//########################### TERM βδ-REDUCTION

//########################### STATEMENTS EXECUTION
/// Evaluates the global statement processing the assignment and pushing to the `environment`
/// the new type binding and substitution
pub fn evaluate_global<T: TypeTheory + Kernel>(
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
                panic!("Evaluating a global definition with ill type body, this should have been caught sooner");
            }
            &body_type.unwrap()
        }
    };
    environment.add_substitution_with_type(var_name, body, var_type);
}

/// Evaluates the function definition statement constructing the signature and pushing to
/// the `enviroment` the name along with the signature and substitution
pub fn evaluate_fun<
    T: TypeTheory,
    C: Fn(&Vec<(String, T::Type)>, &T::Type) -> T::Type,
    E: Fn((String, T::Type), T::Term) -> T::Term,
>(
    environment: &mut Environment<T>,
    fun_name: &str,
    args: &Vec<(String, T::Type)>,
    out_type: &T::Type,
    body: &T::Term,
    _is_rec: &bool,
    fun_type_constructor: C,
    eta_wrap: E,
) -> () {
    let fun_type = fun_type_constructor(args, out_type);
    let body = eta_expand::<T, _>(args, body, eta_wrap);
    environment.add_substitution_with_type(fun_name, &body, &fun_type);
}

/// Evaluates the axiom statement adding the type judgement to the `environment`
pub fn evaluate_axiom<T: TypeTheory>(
    environment: &mut Environment<T>,
    axiom_name: &str,
    formula: &T::Type,
) -> () {
    environment.add_to_context(axiom_name, formula);
}

/// Evaluates the theorem statement, assuming it was already type checked for correctness,
/// and adds the name and formula to the `environment`
pub fn evaluate_theorem<T: TypeTheory, E>(
    environment: &mut Environment<T>,
    theorem_name: &str,
    formula: &T::Type,
    _proof: &Union<T::Term, Vec<Tactic<E>>>,
) -> () {
    environment.add_to_context(&theorem_name, &formula);
}

/// Evaluates the auto statement, clausifying the target formula along with the current context
/// and running SUP saturation algorithm with the clausified set of formulas
pub fn evaluate_auto<
    T: TypeTheory,
    F: Fn(&T::Type) -> Result<Vec<SupFormula>, String>,
    G: Fn(&T::Type) -> T::Type,
>(
    environment: &mut Environment<T>,
    target: &T::Type,
    clausify: F,
    complement: G,
) -> Result<(), String> {
    let mut saturation_set = vec![];
    let context = environment.get_context();

    for (_, var_type) in context.iter() {
        saturation_set.extend(clausify(var_type)?);
    }
    let clausified_target = clausify(&complement(target))?;
    saturation_set.extend(clausified_target);

    Sup::saturate(&saturation_set)
}

/// Evaluates the solve statement by clausifying the negated goals and context hypotheses,
/// running SUP saturation, and returning the answer substitution.
/// Unlike evaluate_auto, this calls saturate directly to recover the Substitution.
pub fn evaluate_solve<
    T: TypeTheory,
    F: Fn(&T::Type) -> Result<Vec<SupFormula>, String>,
    G: Fn(&T::Type) -> T::Type,
>(
    environment: &mut Environment<T>,
    goals: &Vec<T::Type>,
    clausify: F,
    complement: G,
) -> Result<Substitution<SupTerm>, String> {
    let mut saturation_set = vec![];
    let context = environment.get_context();

    for (_, var_type) in context.iter() {
        saturation_set.extend(clausify(var_type)?);
    }
    for goal in goals {
        saturation_set.extend(clausify(&complement(goal))?);
    }

    let selection_fn = get_selection_fn(SelectionFunction::Maximal());
    saturate(&saturation_set, &selection_fn, pick_clause)
}
//########################### STATEMENTS EXECUTION
