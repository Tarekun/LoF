//! CIC refiner: the untrusted layer resolving the holes (`?`) of elaborated
//! terms before they reach the kernel.
//!
//! Terms are walked bidirectionally (`infer`/`check`) the same way the kernel
//! would type check them, but every hole becomes a metavariable declared in
//! the `MetaContext` of the refinement, along with its local context and its
//! (possibly unknown, ie itself a metavariable) type. Wherever the kernel
//! would check a judgemental equality the refiner unifies instead, right
//! away, so metavariables get solved while the locals they might mention are
//! still in scope. Once a refinement is over every metavariable is
//! instantiated with its solution.
//!
//! The output of the refiner is always re-checked by the kernel, which makes
//! no use of any of this machinery.
use super::cic::CicTerm::{
    Abstraction, Application, Let, Match, Meta, Product, Sort, Variable,
};
use super::cic::{Cic, CicTerm, NameKind, HOLE_INDEX};
use super::cic_utils::{
    close_term_as, make_multiarg_fun_type, open_term, pattern_binder_names,
    substitute_and_lift, substitute_local,
};
use super::metavariables::{MetaContext, NameGenerator};
use super::patterns::{
    open_branch, pattern_telescope, with_pattern_entries, PatternEntry,
};
use super::unification::cic_solve_unifications;
use crate::error::LofError;
use crate::misc::Union::{L, R};
use crate::parser::api::Statement;
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::{Reducer, Stm};

/// State of a refinement
#[derive(Debug, Clone, Default)]
pub struct RefinerState {
    /// metavariables of this refinement
    pub metas: MetaContext,
    /// supply of the unique locals binders are opened with
    pub names: NameGenerator,
    /// local context currently in scope (local name, type), outermost first
    locals: Vec<(String, CicTerm)>,
}

impl RefinerState {
    pub fn new() -> Self {
        Self::default()
    }

    /// Brings the local assumptions `locals` in scope
    pub fn enter_locals(&mut self, locals: &[(String, CicTerm)]) {
        self.locals.extend(locals.iter().cloned());
    }

    /// Removes the last `count` local assumptions from the scope
    pub fn exit_locals(&mut self, count: usize) {
        self.locals.truncate(self.locals.len() - count);
    }

    /// Declares a new metavariable of type `typee` in the current local context
    pub fn fresh_meta(&mut self, typee: CicTerm) -> CicTerm {
        self.metas.fresh_meta(self.locals.clone(), typee)
    }

    /// Declares a new metavariable standing for a type in the current local
    /// context
    pub fn fresh_type_meta(&mut self) -> CicTerm {
        self.metas.fresh_type_meta(self.locals.clone())
    }

    /// Unifies `expected ≐ actual`, `origin` describes where the constraint
    /// comes from for error reporting
    pub fn unify(
        &mut self,
        environment: &Environment<Cic>,
        expected: &CicTerm,
        actual: &CicTerm,
        origin: &str,
    ) -> Result<(), LofError> {
        self.unify_metas(environment, expected, actual).map_err(|error| {
            LofError::custom(format!(
                "Refinement failed on {}: expected {:?}, found {:?} ({})",
                origin,
                self.metas.instantiate(expected),
                self.metas.instantiate(actual),
                error
            ))
        })
    }

    /// Solves `expected ≐ actual` with the CIC unification algorithm, and
    /// assigns the metavariables it solved
    fn unify_metas(
        &mut self,
        environment: &Environment<Cic>,
        expected: &CicTerm,
        actual: &CicTerm,
    ) -> Result<(), LofError> {
        let substitution = cic_solve_unifications(
            vec![(self.metas.instantiate(expected), self.metas.instantiate(actual))],
            environment,
        )?;
        for name in substitution.names() {
            // the algorithm also solves (non constant) variables, which are
            // rigid: those solutions are ignored, the kernel rejects whatever
            // mismatch they hide
            let index = match name.strip_prefix("metavariable_") {
                Some(index) => index.parse::<i32>().unwrap(),
                None => continue,
            };
            let value = substitution.get(name).unwrap();
            if !self.metas.is_assigned(&index) {
                self.metas.assign(index, value)?;
            }
        }
        Ok(())
    }

    /// Closes the binder opened with `local` around `term`, giving it back its
    /// user facing `name`. The solved metavariables are instantiated first,
    /// since their solutions might mention `local`
    fn close_binder(&self, term: &CicTerm, local: &str, name: &str) -> CicTerm {
        close_term_as(&self.metas.instantiate(term), local, name)
    }

    /// Instantiates the solutions in `term`. Fails if any metavariable is
    /// left unsolved
    pub fn finalize(&self, term: &CicTerm) -> Result<CicTerm, LofError> {
        let refined = self.metas.instantiate(term);
        self.ensure_no_holes(&refined)?;
        Ok(refined)
    }

    /// Fails if `term` contains a metavariable (out of pattern parameter
    /// positions, which are not holes to be filled but wildcards standing
    /// for the parameters of the matched term)
    pub fn ensure_no_holes(&self, term: &CicTerm) -> Result<(), LofError> {
        match unresolved_metas(term).first() {
            None => Ok(()),
            // TODO(future refiner): unsolved holes are currently rejected,
            // which forbids eg `fun len (l: List(?)) : Nat`, where nothing
            // determines the type of the list elements. A fancier refiner
            // should generalize the metavariables left unsolved in a
            // definition signature into (implicit) polymorphic parameters,
            // ie elaborate it to `fun len (A: TYPE, l: List(A)) : Nat`, and
            // insert the corresponding implicit arguments as fresh holes at
            // every call site (see library/lists.lof for the disabled code)
            Some(index) => Err(LofError::custom(format!(
                "Could not infer hole ?[{}]{} in {:?}",
                index,
                self.metas
                    .meta_type(index)
                    .map(|typee| format!(" of type {:?}", typee))
                    .unwrap_or_default(),
                term
            ))),
        }
    }
}

/// Returns the metavariables (and holes) occurring in `term`, ignoring match
/// patterns (where holes are wildcards)
fn unresolved_metas(term: &CicTerm) -> Vec<i32> {
    fn solver(term: &CicTerm, acc: &mut Vec<i32>) {
        match term {
            Meta(index) => acc.push(*index),
            Sort(_) | Variable(_, _) => {}
            Abstraction(_, l, r) | Product(_, l, r) | Application(l, r) => {
                solver(l, acc);
                solver(r, acc);
            }
            Let(_, t, v, s) => {
                if let Some(t) = t.as_ref() {
                    solver(t, acc);
                }
                solver(v, acc);
                solver(s, acc);
            }
            Match(m, branches) => {
                solver(m, acc);
                for (_, body) in branches {
                    solver(body, acc);
                }
            }
        }
    }
    let mut acc = vec![];
    solver(term, &mut acc);
    acc
}

//########################### SCOPING
/// Runs `callable` with the local assumption `name : typee`
pub fn under_assumption<R, F>(
    environment: &mut Environment<Cic>,
    state: &mut RefinerState,
    name: &str,
    typee: &CicTerm,
    callable: F,
) -> R
where
    F: FnOnce(&mut Environment<Cic>, &mut RefinerState) -> R,
{
    state.locals.push((name.to_string(), typee.to_owned()));
    let result = environment
        .with_local_assumption(name, typee, |local_env| callable(local_env, state));
    state.locals.pop();
    result
}

fn under_definition<R, F>(
    environment: &mut Environment<Cic>,
    state: &mut RefinerState,
    name: &str,
    value: &CicTerm,
    typee: &CicTerm,
    callable: F,
) -> R
where
    F: FnOnce(&mut Environment<Cic>, &mut RefinerState) -> R,
{
    state.locals.push((name.to_string(), typee.to_owned()));
    let result = environment.with_local_substitution(
        name,
        value,
        &Some(typee.to_owned()),
        |local_env| callable(local_env, state),
    );
    state.locals.pop();
    result
}

//########################### SCOPING

//########################### REFINEMENT
/// Infers the type of `term`, returning the refined term along with it.
/// Holes are replaced with fresh metavariables
pub fn infer(
    environment: &mut Environment<Cic>,
    state: &mut RefinerState,
    term: &CicTerm,
) -> Result<(CicTerm, CicTerm), LofError> {
    match term {
        Sort(sort_name) => {
            let sort_type = environment
                .get_variable_type(sort_name)
                .ok_or_else(|| LofError::unbound_variable(sort_name))?;
            Ok((term.to_owned(), sort_type))
        }
        Variable(var_name, NameKind::Bound(dbi)) => Err(LofError::custom(format!(
            "Refiner met the dangling bound variable {}|{}",
            var_name, dbi
        ))),
        Variable(var_name, _) => {
            let var_type = environment
                .get_variable_type(var_name)
                .ok_or_else(|| LofError::unbound_variable(var_name))?;
            Ok((term.to_owned(), var_type))
        }
        // a hole of unknown type: both the hole and its type are unknown
        Meta(HOLE_INDEX) => {
            let meta_type = state.fresh_type_meta();
            let meta = state.fresh_meta(meta_type.clone());
            Ok((meta, meta_type))
        }
        Meta(index) => {
            let meta_type = state.metas.meta_type(index).ok_or_else(|| {
                LofError::custom(format!(
                    "Metavariable ?[{}] is not declared in the context of this refinement",
                    index
                ))
            })?;
            Ok((term.to_owned(), meta_type))
        }
        Abstraction(var_name, var_type, body) => {
            let var_type = refine_type(environment, state, var_type)?;
            let local = state.names.fresh_local_name(var_name);
            let opened_body = open_term(body, &local);
            let (body, body_type) =
                under_assumption(environment, state, &local, &var_type, |env, st| {
                    infer(env, st, &opened_body)
                })?;

            Ok((
                Abstraction(
                    var_name.to_owned(),
                    Box::new(var_type.clone()),
                    Box::new(state.close_binder(&body, &local, var_name)),
                ),
                Product(
                    var_name.to_owned(),
                    Box::new(var_type),
                    Box::new(state.close_binder(&body_type, &local, var_name)),
                ),
            ))
        }
        Product(var_name, domain, codomain) => {
            let domain = refine_type(environment, state, domain)?;
            let local = state.names.fresh_local_name(var_name);
            let opened_codomain = open_term(codomain, &local);
            let (codomain, codomain_sort) =
                under_assumption(environment, state, &local, &domain, |env, st| {
                    let (codomain, codomain_sort) = infer(env, st, &opened_codomain)?;
                    let codomain_sort = Cic::normalize_term(env, &codomain_sort);
                    ensure_sort(&codomain, &codomain_sort)?;
                    Ok::<_, LofError>((codomain, codomain_sort))
                })?;

            Ok((
                Product(
                    var_name.to_owned(),
                    Box::new(domain),
                    Box::new(state.close_binder(&codomain, &local, var_name)),
                ),
                codomain_sort,
            ))
        }
        Application(function, argument) => {
            let (function, function_type) = infer(environment, state, function)?;
            let function_type = Cic::normalize_term(
                environment,
                &state.metas.instantiate(&function_type),
            );
            match function_type {
                Product(var_name, domain, codomain) => {
                    let argument = check(
                        environment,
                        state,
                        argument,
                        &domain,
                        &format!("argument {:?} of {:?}", argument, function),
                    )?;
                    let result_type =
                        substitute_and_lift(&codomain, &var_name, &argument);
                    Ok((
                        Application(Box::new(function), Box::new(argument)),
                        result_type,
                    ))
                }
                other => Err(LofError::custom(format!(
                    "Cannot apply {:?} of type {:?}: it's not a function, or its type cannot be inferred (add a type annotation)",
                    function, other
                ))),
            }
        }
        Let(var_name, var_type, value, scope) => {
            let (value, refined_var_type, definition_type) = match &**var_type {
                Some(var_type) => {
                    let var_type = refine_type(environment, state, var_type)?;
                    let value = check(
                        environment,
                        state,
                        value,
                        &var_type,
                        &format!("let binding `{}`", var_name),
                    )?;
                    (value, Some(var_type.clone()), var_type)
                }
                None => {
                    let (value, value_type) = infer(environment, state, value)?;
                    (value, None, value_type)
                }
            };
            let local = state.names.fresh_local_name(var_name);
            let opened_scope = open_term(scope, &local);
            let (scope, scope_type) = under_definition(
                environment,
                state,
                &local,
                &value,
                &definition_type,
                |env, st| infer(env, st, &opened_scope),
            )?;

            Ok((
                Let(
                    var_name.to_owned(),
                    Box::new(refined_var_type),
                    Box::new(value.clone()),
                    Box::new(state.close_binder(&scope, &local, var_name)),
                ),
                substitute_local(
                    &state.metas.instantiate(&scope_type),
                    &local,
                    &value,
                ),
            ))
        }
        Match(matched_term, branches) => {
            infer_match(environment, state, matched_term, branches)
        }
    }
}

fn infer_match(
    environment: &mut Environment<Cic>,
    state: &mut RefinerState,
    matched_term: &CicTerm,
    branches: &Vec<(CicTerm, CicTerm)>,
) -> Result<(CicTerm, CicTerm), LofError> {
    let (matched_term, matched_type) = infer(environment, state, matched_term)?;
    let matched_type = Cic::normalize_term(
        environment,
        &state.metas.instantiate(&matched_type),
    );
    if let Meta(_) = matched_type {
        return Err(LofError::custom(format!(
            "Cannot infer the type of the matched term {:?} (add a type annotation)",
            matched_term
        )));
    }

    let mut return_type: Option<CicTerm> = None;
    let mut refined_branches = vec![];
    for (pattern, body) in branches {
        let (opened_pattern, opened_body, locals) =
            open_branch(pattern, body, |name| state.names.fresh_local_name(name));
        let (constructor, entries) =
            pattern_telescope(environment, &opened_pattern, &matched_type)?;
        let pattern_locals: Vec<(String, CicTerm)> = entries
            .iter()
            .map(|entry| match entry {
                PatternEntry::Assume(name, typee)
                | PatternEntry::Define(name, _, typee) => {
                    (name.to_owned(), typee.to_owned())
                }
            })
            .collect();
        state.enter_locals(&pattern_locals);
        let branch = with_pattern_entries(environment, &entries, |env| {
            let (body, body_type) = infer(env, state, &opened_body)?;
            // aliases of the parameters are only defined in here
            Ok::<_, LofError>((body, Cic::normalize_term(env, &body_type)))
        });
        state.exit_locals(pattern_locals.len());
        let (body, body_type) = branch?;

        match &return_type {
            None => return_type = Some(body_type),
            Some(expected) => state.unify(
                environment,
                expected,
                &body_type,
                &format!("branch for constructor {}", constructor),
            )?,
        }

        // close the telescope back, outermost binder first
        let (pattern, body) = locals
            .iter()
            .zip(pattern_binder_names(pattern))
            .fold((opened_pattern, body), |(pattern, body), (local, name)| {
                (
                    state.close_binder(&pattern, local, &name),
                    state.close_binder(&body, local, &name),
                )
            });
        refined_branches.push((pattern, body));
    }

    let return_type = return_type.ok_or_else(|| {
        LofError::type_check_error(&format!(
            "Cannot compute the type of the match on {:?} without branches",
            matched_term
        ))
    })?;
    Ok((Match(Box::new(matched_term), refined_branches), return_type))
}

/// Checks `term` against the `expected` type, returning the refined term.
/// `origin` describes what is being checked, for error reporting
pub fn check(
    environment: &mut Environment<Cic>,
    state: &mut RefinerState,
    term: &CicTerm,
    expected: &CicTerm,
    origin: &str,
) -> Result<CicTerm, LofError> {
    let expected =
        Cic::normalize_term(environment, &state.metas.instantiate(expected));
    match (term, &expected) {
        // a hole checked against a type is a metavariable of that type
        (Meta(HOLE_INDEX), _) => Ok(state.fresh_meta(expected)),
        // the expected codomain is pushed under the binder, so that the
        // metavariables of the body are solved while the binder is in scope
        (Abstraction(var_name, var_type, body), Product(_, domain, codomain)) => {
            let var_type = refine_type(environment, state, var_type)?;
            state.unify(environment, domain, &var_type, origin)?;
            let local = state.names.fresh_local_name(var_name);
            let opened_body = open_term(body, &local);
            let opened_codomain = open_term(codomain, &local);
            let body =
                under_assumption(environment, state, &local, &var_type, |env, st| {
                    check(env, st, &opened_body, &opened_codomain, origin)
                })?;

            Ok(Abstraction(
                var_name.to_owned(),
                Box::new(var_type),
                Box::new(state.close_binder(&body, &local, var_name)),
            ))
        }
        _ => {
            let (refined, actual) = infer(environment, state, term)?;
            state.unify(environment, &expected, &actual, origin)?;
            Ok(refined)
        }
    }
}

/// Refines `typee`, making sure it actually is a type (ie its type is a sort)
pub fn refine_type(
    environment: &mut Environment<Cic>,
    state: &mut RefinerState,
    typee: &CicTerm,
) -> Result<CicTerm, LofError> {
    if let Meta(HOLE_INDEX) = typee {
        return Ok(state.fresh_type_meta());
    }
    let (refined, sort) = infer(environment, state, typee)?;
    let sort = Cic::normalize_term(environment, &state.metas.instantiate(&sort));
    ensure_sort(&refined, &sort)?;
    Ok(refined)
}

fn ensure_sort(typee: &CicTerm, sort: &CicTerm) -> Result<(), LofError> {
    match sort {
        // a hole in type position has a yet unknown sort
        Sort(_) | Meta(_) => Ok(()),
        _ => Err(LofError::type_mismatch("refinement of a type", &"a sort", typee)),
    }
}
//########################### REFINEMENT

//########################### STATEMENTS
/// Refines a standalone expression
pub fn refine_expression(
    environment: &mut Environment<Cic>,
    term: &CicTerm,
) -> Result<CicTerm, LofError> {
    let mut state = RefinerState::new();
    let (refined, _) = infer(environment, &mut state, term)?;
    state.finalize(&refined)
}

/// Refines a closed type
fn refine_closed_type(
    environment: &mut Environment<Cic>,
    typee: &CicTerm,
) -> Result<CicTerm, LofError> {
    let mut state = RefinerState::new();
    let refined = refine_type(environment, &mut state, typee)?;
    state.finalize(&refined)
}

/// Refines a function definition as the term it stands for, ie the
/// abstraction `λargs. body` checked against the product `Πargs. out_type`:
/// the arguments are bound in the signature and in the body exactly as they
/// would be by those binders
fn refine_fun(
    environment: &mut Environment<Cic>,
    fun_name: &str,
    args: &Vec<(String, CicTerm)>,
    out_type: &CicTerm,
    body: &CicTerm,
    is_rec: &bool,
) -> Result<Stm<Cic>, LofError> {
    let mut state = RefinerState::new();
    let origin = format!("body of function `{}`", fun_name);
    let fun_type = make_multiarg_fun_type(args, out_type);
    let fun_type = refine_type(environment, &mut state, &fun_type)?;
    let lambda = args.iter().rev().fold(body.to_owned(), |body, (name, typee)| {
        Abstraction(name.to_owned(), Box::new(typee.to_owned()), Box::new(body))
    });
    let lambda = if *is_rec {
        // the recursive reference is added with whatever holes the
        // signature still has
        under_assumption(environment, &mut state, fun_name, &fun_type, |env, st| {
            check(env, st, &lambda, &fun_type, &origin)
        })?
    } else {
        check(environment, &mut state, &lambda, &fun_type, &origin)?
    };

    // split the refined signature and abstraction back into their parts
    let mut out_type = state.finalize(&fun_type)?;
    let mut body = state.finalize(&lambda)?;
    let mut refined_args = vec![];
    for _ in args {
        match (out_type, body) {
            (Product(name, arg_type, codomain), Abstraction(_, _, scope)) => {
                refined_args.push((name, *arg_type));
                out_type = *codomain;
                body = *scope;
            }
            _ => unreachable!("refinement preserves the binders of the function"),
        }
    }

    Ok(Statement::Fun(
        fun_name.to_string(),
        refined_args,
        Box::new(out_type),
        Box::new(body),
        *is_rec,
    ))
}

/// Refines a statement: resolves all its holes
pub fn refine_statement(
    environment: &mut Environment<Cic>,
    stm: &Stm<Cic>,
) -> Result<Stm<Cic>, LofError> {
    match stm {
        Statement::Global(var_name, opt_type, body) => {
            let mut state = RefinerState::new();
            let (body, var_type) = match opt_type {
                Some(var_type) => {
                    let var_type = refine_type(environment, &mut state, var_type)?;
                    let body = check(
                        environment,
                        &mut state,
                        body,
                        &var_type,
                        &format!("global `{}`", var_name),
                    )?;
                    (body, var_type)
                }
                None => infer(environment, &mut state, body)?,
            };
            let body = state.finalize(&body)?;
            let var_type = state.finalize(&var_type)?;
            Ok(Statement::Global(var_name.to_owned(), Some(var_type), body))
        }
        Statement::Axiom(axiom_name, formula) => Ok(Statement::Axiom(
            axiom_name.to_owned(),
            refine_closed_type(environment, formula)?,
        )),
        Statement::Fun(fun_name, args, out_type, body, is_rec) => {
            refine_fun(environment, fun_name, args, out_type, body, is_rec)
        }
        Statement::Inductive(type_name, params, ariety, constructors) => {
            let has_holes = params
                .iter()
                .chain(constructors.iter())
                .map(|(_, typee)| typee)
                .chain(std::iter::once(&**ariety))
                .any(|typee| !unresolved_metas(typee).is_empty());
            if has_holes {
                Err(LofError::custom(format!(
                    "Holes are not supported in the definition of inductive type {}",
                    type_name
                )))
            } else {
                Ok(stm.to_owned())
            }
        }
        Statement::Theorem(theorem_name, formula, proof) => {
            let formula = refine_closed_type(environment, formula)?;
            let proof = match proof {
                L(proof_term) => {
                    let mut state = RefinerState::new();
                    let proof_term = check(
                        environment,
                        &mut state,
                        proof_term,
                        &formula,
                        &format!("proof of theorem `{}`", theorem_name),
                    )?;
                    L(state.finalize(&proof_term)?)
                }
                // tactic proofs are run by the kernel
                R(tactics) => R(tactics.to_owned()),
            };
            Ok(Statement::Theorem(theorem_name.to_owned(), formula, proof))
        }
        _ => Ok(stm.to_owned()),
    }
}

//########################### STATEMENTS

#[cfg(test)]
#[path = "../../tests/type_theory/cic/refiner.rs"]
mod tests;
