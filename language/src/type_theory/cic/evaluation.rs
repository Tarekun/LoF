use super::cic::CicStm::{Axiom, Fun, Global, Theorem};
use super::cic::CicTerm::{
    Abstraction, Application, Let, Match, Product, Sort, Variable,
};
use super::cic::{Cic, CicStm, CicTerm, GLOBAL_INDEX};
use super::cic_utils::{index_variables, make_multiarg_fun_type};
use super::transport::transport_definition;
use crate::error::LofError;
use crate::type_theory::cic::cic_utils::{
    apply_arguments, application_args, get_applied_function, is_instance_of,
    substitute,
};
use crate::type_theory::cic::type_check::inductive_eliminator;
use crate::type_theory::commons::evaluation::{
    evaluate_axiom, evaluate_fun, evaluate_global, evaluate_theorem,
    reduce_application, reduce_let, reduce_variable,
};
use crate::type_theory::commons::transport::EquivConfig;
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::{Kernel, Reducer, Refiner};
use std::collections::HashMap;

//########################### TERM βδ-REDUCTION
pub fn one_step_reduction(
    environment: &Environment<Cic>,
    term: &CicTerm,
) -> CicTerm {
    match term {
        Variable(var_name, _) => {
            reduce_variable::<Cic>(environment, var_name, term)
        }
        Application(left, right) => {
            // ι-reduction first: an `e_<Type>` application whose final
            // (instance) argument is a concrete constructor computes to
            // the matching per-constructor case. Falls through to ordinary
            // β/δ-reduction when that doesn't apply.
            if let Some(iota_reduced) =
                try_reduce_eliminator_application(environment, term)
            {
                return iota_reduced;
            }

            reduce_application::<Cic, _, _>(
                environment,
                left,
                right,
                |fun_reduced| match fun_reduced {
                    Abstraction(var_name, _, body) => {
                        Some((var_name.to_string(), (**body).to_owned()))
                    }
                    _ => None,
                },
                |left_reduced, right_reduced| {
                    Application(Box::new(left_reduced), Box::new(right_reduced))
                },
            )
        }
        Let(var_name, var_type, body, scope) => {
            reduce_let(environment, var_name, var_type, body, scope)
        }
        Match(matched_term, branches) => {
            reduce_match(environment, matched_term, branches)
        }
        // Descend into a dependent function type's domain/codomain (resp.
        // an abstraction's domain/body) so a redex embedded there - eg a
        // motive applied to a bound variable, exactly what an eliminator's
        // generated minor-premise/conclusion types produce - gets reduced
        // too. Without this, two Pi-types that are only equal up to
        // reducing an under-binder application (the routine case for any
        // dependent induction proof) are never recognized as such, since
        // unification normalizes both sides before comparing them.
        //
        // Note these take a *single* step on each component rather than
        // normalizing it outright: `generic_term_normalization` already
        // iterates to a fixed point, so a nested full normalization here
        // would redo that inner fixpoint on every outer iteration, making
        // the total work exponential in the term's binder depth.
        Product(var_name, domain, codomain) => Product(
            var_name.to_string(),
            Box::new(one_step_reduction(environment, domain)),
            Box::new(one_step_reduction(environment, codomain)),
        ),
        Abstraction(var_name, domain, body) => Abstraction(
            var_name.to_string(),
            Box::new(one_step_reduction(environment, domain)),
            Box::new(one_step_reduction(environment, body)),
        ),
        _ => term.clone(),
    }
}
//
//
/// ι-reduction for an auto-generated eliminator: given a fully applied
/// `e_<Type>(params.., motive, case_1..case_k, instance)` whose `instance`
/// is a concrete constructor application `ctor_i(params.., args..)`,
/// computes to `case_i` applied to those args, with an induction
/// hypothesis (the same eliminator re-applied to the sub-term) inserted
/// after each recursive argument - exactly the computation rule
/// `inductive_eliminator` builds the eliminator's *type* around.
///
/// Without this, `e_<Type>` applications are permanently stuck: they type
/// check but never compute, so anything *defined* through an eliminator
/// (rather than through a `match`) has no definitional behaviour at all,
/// and even a ground fact like `plus_via_elim(z,z) = z` becomes unprovable
/// by reflexivity.
///
/// Indexed families are handled too: the index count is recovered from the
/// application's own arity, and a recursive occurrence's induction
/// hypothesis is rebuilt with that occurrence's *own* index values (read
/// off its type after substituting the constructor's earlier arguments, so
/// eg `vcons`'s recursive `Vec(T,n)` argument yields `n`, not the outer
/// `s(n)`).
fn try_reduce_eliminator_application(
    environment: &Environment<Cic>,
    term: &CicTerm,
) -> Option<CicTerm> {
    let head = get_applied_function(term);
    let elim_name = match &head {
        Variable(name, dbi)
            if *dbi == GLOBAL_INDEX && name.starts_with("e_") =>
        {
            name.to_owned()
        }
        _ => return None,
    };
    let type_name = elim_name.strip_prefix("e_")?.to_string();
    let param_count = environment.get_inductive_param_count(&type_name)?;
    let constructors = environment.constructor_store.get(&type_name)?;
    let constructor_count = constructors.len();

    // layout: params, motive, one case per constructor, indices, instance
    let args = application_args(term);
    let fixed_args = param_count + 1 + constructor_count + 1;
    if args.len() < fixed_args {
        // still a partial application - nothing to compute yet
        return None;
    }

    let instance = args.last()?;
    let instance_head = get_applied_function(instance);
    let constructor_name = match &instance_head {
        Variable(name, dbi) if *dbi == GLOBAL_INDEX => name.to_owned(),
        // the scrutinee isn't constructor-headed (eg a bound variable):
        // genuinely stuck, not reducible
        _ => return None,
    };
    let constructor_index = constructors
        .iter()
        .position(|(name, _)| name == &constructor_name)?;
    let constructor_type = constructors[constructor_index].1.to_owned();

    let case = args[param_count + 1 + constructor_index].to_owned();
    // params + motive + every case: what an induction hypothesis re-applies
    // the eliminator to, before that occurrence's own indices and the
    // recursive sub-term itself
    let leading_args = args[..param_count + 1 + constructor_count].to_vec();

    let instance_args = application_args(instance);
    if instance_args.len() < param_count {
        return None;
    }
    let own_args = &instance_args[param_count..];

    // Walk the constructor's Pi-chain alongside the arguments actually
    // supplied, substituting as we go, so each argument's type is stated in
    // terms of concrete values rather than the constructor's own binders.
    let mut remaining_type = constructor_type;
    let mut own_arg_types = vec![];
    for supplied in instance_args.iter() {
        match remaining_type {
            Product(binder, domain, codomain) => {
                own_arg_types.push((*domain).to_owned());
                remaining_type = substitute(&codomain, &binder, supplied);
            }
            // fewer Pi layers than supplied arguments: not a shape this
            // rule understands
            _ => return None,
        }
    }
    if own_arg_types.len() != instance_args.len() {
        return None;
    }
    let own_arg_types = &own_arg_types[param_count..];

    let mut reduced = case;
    for (own_arg, own_arg_type) in own_args.iter().zip(own_arg_types.iter()) {
        reduced =
            Application(Box::new(reduced), Box::new(own_arg.to_owned()));

        if is_instance_of(own_arg_type, &type_name) {
            // this occurrence's own indices, ie whatever `Type(params.., i..)`
            // it is an instance of, minus the (uniform) parameters
            let occurrence_args = application_args(own_arg_type);
            if occurrence_args.len() < param_count {
                return None;
            }
            let occurrence_indices = &occurrence_args[param_count..];

            let mut hypothesis_args = leading_args.clone();
            hypothesis_args.extend(occurrence_indices.iter().cloned());
            hypothesis_args.push(own_arg.to_owned());
            let induction_hypothesis = apply_arguments(
                &Variable(elim_name.to_owned(), GLOBAL_INDEX),
                hypothesis_args,
            );
            reduced = Application(
                Box::new(reduced),
                Box::new(induction_hypothesis),
            );
        }
    }

    Some(reduced)
}
//
//
fn reduce_match(
    environment: &Environment<Cic>,
    matched_term: &CicTerm,
    branches: &Vec<(CicTerm, CicTerm)>,
) -> CicTerm {
    let normalized_term = Cic::normalize_term(environment, matched_term);
    for (pattern, body) in branches {
        if matches_pattern(&normalized_term, pattern) {
            return substitute_pattern_variables(
                &normalized_term,
                pattern,
                body,
            );
        }
    }

    // The scrutinee normalized to something that isn't headed by any of
    // this match's constructors - eg an open/bound variable (as happens
    // routinely inside an inductive proof's step case, where the scrutinee
    // is a locally-bound predecessor rather than a concrete constructor
    // application). This is a stuck redex, not an error: exhaustiveness
    // over the matched type's constructors is already enforced separately
    // at type-checking time (`type_check_match`), so a *concrete*
    // (constructor-headed) scrutinee is always covered by some branch;
    // only an irreducible/open scrutinee can reach here, and the match
    // itself is its normal form.
    Match(Box::new(normalized_term), branches.to_owned())
}
//########################### TERM βδ-REDUCTION

//########################### STATEMENTS EXECUTION
pub fn evaluate_statement(
    environment: &mut Environment<Cic>,
    stm: &CicStm,
) -> Result<(), LofError> {
    match stm {
        Axiom(axiom_name, formula) => {
            evaluate_axiom::<Cic>(environment, axiom_name, formula)
        }
        Global(var_name, var_type, body) => {
            evaluate_global::<Cic>(environment, var_name, var_type, body)
        }
        Fun(fun_name, args, out_type, body, is_rec) => {
            evaluate_fun::<Cic, _, _>(
                environment,
                fun_name,
                args,
                out_type,
                body,
                is_rec,
                |args, out_type| make_multiarg_fun_type(args, out_type),
                |(var_name, var_type), body| {
                    Abstraction(var_name, Box::new(var_type), Box::new(body))
                },
            )
        }
        Theorem(theorem_name, formula, proof) => {
            evaluate_theorem::<Cic, CicTerm>(
                environment,
                theorem_name,
                formula,
                proof,
            )
        }
        CicStm::InductiveDef(type_name, params, ariety, constructors) => {
            evaluate_inductive(
                environment,
                type_name,
                params,
                ariety,
                constructors,
            )
        }
    }
}
//
//
pub fn evaluate_inductive(
    environment: &mut Environment<Cic>,
    name: &str,
    params: &Vec<(String, CicTerm)>,
    ariety: &CicTerm,
    constructors: &Vec<(String, CicTerm)>,
) -> Result<(), LofError> {
    let ind_type = make_multiarg_fun_type(params, ariety);
    environment.add_to_context(name, &ind_type);

    let mut constr_set = vec![];
    for (constr_name, constr_type) in constructors {
        let constr_type = make_multiarg_fun_type(&params, constr_type);
        environment.add_to_context(constr_name, &constr_type);
        constr_set.push((constr_name.to_string(), constr_type));
    }

    environment.add_to_context(
        &format!("e_{}", name),
        &inductive_eliminator(
            name.to_string(),
            params.to_owned(),
            ariety.to_owned(),
            constructors.to_owned(),
        ),
    );
    environment.add_constructor_store(name, constr_set);
    // recorded so `try_reduce_eliminator_application` can locate the
    // motive/cases/instance inside an `e_<name>` application by position
    environment.add_inductive_param_count(name, params.len());

    Ok(())
}
//########################### STATEMENTS EXECUTION
//
//########################### HELPER FUNCTIONS
/// Given a `term` and a `pattern`, returns `true` if the term matches the
/// pattern, `false` otherwise
fn matches_pattern(term: &CicTerm, pattern: &CicTerm) -> bool {
    let used = get_applied_function(term);
    let constructor = get_applied_function(pattern);
    let actual_args = application_args(term);
    let formal_args = application_args(pattern);

    // TODO i think this should match the types as well but im not sure
    return (used == constructor) && (actual_args.len() == formal_args.len());
}

/// Given the matched `term` and the `pattern`, substitutes every pattern
/// variable the corresponding expression from `term` inside `body`
fn substitute_pattern_variables(
    term: &CicTerm,
    pattern: &CicTerm,
    body: &CicTerm,
) -> CicTerm {
    let actual_args = application_args(term);
    let formal_args = application_args(pattern);

    formal_args.iter().zip(actual_args.iter()).fold(
        body.clone(),
        |bound_body, (formal_arg, actual_arg)| {
            substitute_pattern_arg(formal_arg, actual_arg, &bound_body)
        },
    )
}

/// Substitutes a single `formal_arg` from a pattern with the corresponding `actual_arg`
fn substitute_pattern_arg(
    formal_arg: &CicTerm,
    actual_arg: &CicTerm,
    body: &CicTerm,
) -> CicTerm {
    match formal_arg {
        Variable(var_name, _) => substitute(body, var_name, actual_arg),
        Application(_, _) => {
            substitute_pattern_variables(actual_arg, formal_arg, body)
        }
        // metavariables (`?`) and other patterns bind nothing
        _ => body.clone(),
    }
}
//########################### HELPER FUNCTIONS

#[cfg(test)]
#[path = "../../tests/type_theory/cic/evaluation.rs"]
mod tests;

