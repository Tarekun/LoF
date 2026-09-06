use super::cic::CicTerm::{
    Abstraction, Application, Let, Match, Meta, Product, Sort, Variable,
};
use super::cic::{Cic, CicTerm};
use crate::misc::simple_map;
use crate::type_theory::cic::cic::{
    FIRST_INDEX, GLOBAL_INDEX, PLACEHOLDER_DBI,
};
use crate::type_theory::commons::unification::Substitution;
use crate::type_theory::commons::utils::generic_multiarg_fun_type;
use std::collections::HashMap;
use std::fmt;

fn term_formatter(term: &CicTerm, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match term {
        // (sort name)
        Sort(name) => write!(f, "{}", name),
        // (var name)
        Variable(name, dbi) => {
            let dbi_text = if *dbi == GLOBAL_INDEX {
                "G"
            } else if *dbi == PLACEHOLDER_DBI {
                "P"
            } else {
                &dbi.to_string()
            };
            write!(f, "{}|{}", name, dbi_text)
        }
        Abstraction(var_name, var_type, body) => {
            write!(f, "λ{}:{}. {}", var_name, var_type, body)
        }
        Product(var_name, domain, codomain) => {
            write!(f, "Π{}:{}. {}", var_name, domain, codomain)
        }
        Application(func, arg) => write!(f, "({} {})", func, arg),
        // (matched_term, [ branch: ([pattern], body) ])
        Match(matched_term, branches) => {
            write!(f, "match {} {{ ", matched_term)?;
            for (pattern, body) in branches {
                write!(f, "\t[{}] => {},\n", pattern, body)?;
            }
            write!(f, "}}")
        }
        Let(var_name, _, body, scope) => {
            write!(f, "let {} := {} in\n{}", var_name, body, scope)
        }
        Meta(index) => write!(f, "?[{}]", index),
    }
}
impl fmt::Display for CicTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        term_formatter(self, f)
    }
}
impl fmt::Debug for CicTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        term_formatter(self, f)
    }
}
/// Given the CIC type of a function `fun` returns the number of arguments of the function
// pub fn args_len(fun: &CicTerm) -> i32 {
//     match fun {
//         Product(_, _, codomain) => 1 + args_len(codomain),
//         _ => 0,
//     }
// }

/// Returns variable terms from a multi argument function
pub fn get_variables_as_terms(fun_type: &CicTerm) -> Vec<CicTerm> {
    fn solver(fun_type: &CicTerm, index: i32) -> Vec<CicTerm> {
        match fun_type {
            Product(var_name, _domain, codomain) => {
                let mut rec: Vec<CicTerm> = solver(codomain, index + 1);
                let mut result = vec![Variable(var_name.to_owned(), index)];
                result.append(&mut rec);
                result
            }
            _ => {
                vec![] //discard the base type
            }
        }
    }

    solver(fun_type, 0)
}

/// Returns the list of types of the arguments of a multi arg function
pub fn get_arg_types(fun_type: &CicTerm) -> Vec<CicTerm> {
    match fun_type {
        Product(_, domain, codomain) => {
            let mut result: Vec<CicTerm> = vec![(**domain).clone()];
            result.extend(get_arg_types(&codomain));
            return result;
        }
        _ => vec![],
    }
}

/// Like `get_arg_types`, but keeps each argument's binder name alongside its
/// domain type (eg. so callers can tell which arguments are the ones a prior
/// unification already solved for by name, rather than genuine remaining
/// premises).
pub fn get_named_arg_types(fun_type: &CicTerm) -> Vec<(String, CicTerm)> {
    match fun_type {
        Product(var_name, domain, codomain) => {
            let mut result = vec![(var_name.to_owned(), (**domain).clone())];
            result.extend(get_named_arg_types(codomain));
            return result;
        }
        _ => vec![],
    }
}

/// Takes a function term and returns an application term of all the arguments given
pub fn apply_arguments(fun: &CicTerm, args: Vec<CicTerm>) -> CicTerm {
    let mut application = fun.clone();
    for arg in args {
        application = Application(Box::new(application), Box::new(arg));
    }

    application
}

/// Clones the given product, swapping the innermost body term with the given one
pub fn clone_product_with_different_result(
    product: &CicTerm,
    new_result: CicTerm,
) -> CicTerm {
    match product {
        Product(var_name, domain, codomain) => {
            let new_codomain =
                clone_product_with_different_result(codomain, new_result);
            Product(var_name.to_owned(), domain.clone(), Box::new(new_codomain))
        }
        Sort(_) => new_result,
        Variable(_, _) => new_result,
        _ => panic!("TODO: handle better"),
    }
}

/// Returns whether `term` is the canonical placeholder produced by
/// `Cic::proof_hole()`, marking a not-yet-solved subgoal inside a partial
/// proof term.
fn is_proof_hole(term: &CicTerm) -> bool {
    matches!(term, Sort(name) if name == "THIS_IS_A_PARTIAL_PROOF_HOLE")
}

/// Searches `proof_term` for the leftmost (in left-to-right, depth-first
/// order) proof hole and, if found, returns the term with that hole replaced
/// by `new_body`. Returns `None` when `proof_term` contains no hole at all,
/// so callers composing multiple subterms (eg. both sides of an
/// `Application`) can try the next one.
///
/// A partial proof may contain several holes at once (eg. after `apply`-ing
/// a lemma with more than one premise, one hole per premise is introduced),
/// so this only ever touches the first one, leaving the rest of the term -
/// and any other pending holes in it - untouched.
fn try_swap_proof_hole(
    proof_term: &CicTerm,
    new_body: &CicTerm,
) -> Option<CicTerm> {
    if is_proof_hole(proof_term) {
        return Some(new_body.to_owned());
    }
    match proof_term {
        Abstraction(var_name, var_type, body) => {
            try_swap_proof_hole(body, new_body).map(|new_body| {
                Abstraction(
                    var_name.to_owned(),
                    var_type.clone(),
                    Box::new(new_body),
                )
            })
        }
        Application(left, right) => {
            match try_swap_proof_hole(left, new_body) {
                Some(new_left) => {
                    Some(Application(Box::new(new_left), right.clone()))
                }
                None => try_swap_proof_hole(right, new_body).map(|new_right| {
                    Application(left.clone(), Box::new(new_right))
                }),
            }
        }
        _ => None,
    }
}

/// Clones the given `proof_term`, swapping the (leftmost) hole with the
/// given `new_body`. Panics if `proof_term` contains no hole to swap.
pub fn swap_proof_hole(proof_term: &CicTerm, new_body: &CicTerm) -> CicTerm {
    try_swap_proof_hole(proof_term, new_body).unwrap_or_else(|| {
        panic!(
            "swap_proof_hole: no partial-proof hole found in {:?}",
            proof_term
        )
    })
}

/// Returns the innermost body term of a serie of concatenated Products
/// (ie the return type of a function)
pub fn get_prod_innermost(term: &CicTerm) -> &CicTerm {
    match term {
        Product(_, _, codomain) => get_prod_innermost(&*codomain),
        _ => term,
    }
}

/// Given a multiarg application term, returns the vector of all the arguments being applyed
pub fn application_args(application: &CicTerm) -> Vec<CicTerm> {
    match application {
        Application(left, right) => {
            let mut rec = application_args(left);
            rec.push((**right).to_owned()); //TODO shouldnt it be append/enqueue?
            return rec;
        }
        // discard leftmost term, we dont care about the function
        _ => vec![],
    }
}

/// Given a multiarg application term, returns the innermost term element (ie the function
/// being applied)
pub fn get_applied_function(application: &CicTerm) -> CicTerm {
    match application {
        Application(left, _) => get_applied_function(left),
        _ => application.to_owned(),
    }
}

/// Returns `true` if `term` is an instance of type with name `name`, `false` otherwise
pub fn is_instance_of(term: &CicTerm, name: &str) -> bool {
    match term {
        Variable(var_name, _) => var_name == name,
        Application(dep_type, _args) => is_instance_of(&dep_type, name),
        // anything else isnt a referencable type
        _ => false,
    }
}

/// Returns `true` if `term` corresponds to a constant symbol, `false` otherwise
pub fn is_constant(term: &CicTerm) -> bool {
    match term {
        Variable(_, dbi) => *dbi == GLOBAL_INDEX,
        _ => false,
    }
}

/// Given a `term` returns `true` if it contains a reference to the variable `name`
pub fn references(term: &CicTerm, name: &str) -> bool {
    match term {
        Variable(var_name, _) => var_name == name,
        Sort(sort_name) => sort_name == name,
        Application(left, rigth) => {
            references(&left, name) || references(&rigth, name)
        }
        Abstraction(_, domain, codomain) => {
            references(&domain, name) || references(&codomain, name)
        }
        Product(_, domain, codomain) => {
            references(&domain, name) || references(&codomain, name)
        }
        // TODO fuck match fr
        _ => false,
    }
}

/// Returns `true` if `name` occurs only positively in `rec_type`, `false` otherwise
pub fn check_positivity(function_type: &CicTerm, name: &str) -> bool {
    let arg_types = get_arg_types(function_type);
    for arg_type in arg_types {
        if references(&arg_type, name) {
            return false;
        }
    }

    true
}

/// Returns `term` where each instance of the meta variable `target` is swapped with `arg`
pub fn substitute_meta(term: &CicTerm, target: &i32, arg: &CicTerm) -> CicTerm {
    match term {
        Meta(index) => {
            if index == target {
                arg.clone()
            } else {
                term.clone()
            }
        }
        Sort(_) => term.clone(),
        Variable(_, _) => term.clone(),
        Application(left, right) => Application(
            Box::new(substitute_meta(left, target, arg)),
            Box::new(substitute_meta(right, target, arg)),
        ),
        Abstraction(var_name, domain, codomain) => Abstraction(
            var_name.to_string(),
            Box::new(substitute_meta(domain, target, arg)),
            Box::new(substitute_meta(codomain, target, arg)),
        ),
        Product(var_name, domain, codomain) => Product(
            var_name.to_string(),
            Box::new(substitute_meta(domain, target, arg)),
            Box::new(substitute_meta(codomain, target, arg)),
        ),
        Let(var_name, var_type, body, scope) => Let(
            var_name.to_string(),
            Box::new(if var_type.is_some() {
                Some(substitute_meta(
                    (**var_type).as_ref().unwrap(),
                    target,
                    arg,
                ))
            } else {
                None
            }),
            Box::new(substitute_meta(body, target, arg)),
            Box::new(substitute_meta(scope, target, arg)),
        ),
        Match(matched_term, branches) => Match(
            Box::new(substitute_meta(matched_term, target, arg)),
            //TODO i dont want to clone branches here tbh
            simple_map(branches.clone(), |(pattern, body)| {
                (
                    substitute_meta(&pattern, target, arg),
                    substitute_meta(&body, target, arg),
                )
            }),
        ),
    }
}

/// Given a `term` and a variable, returns a term where each instance of
/// `var_name` is substituted with `arg`
pub fn substitute(term: &CicTerm, target_name: &str, arg: &CicTerm) -> CicTerm {
    match term {
        Sort(_) => term.clone(),
        Variable(var_name, _) => {
            if var_name == target_name {
                arg.clone()
            } else {
                term.clone()
            }
        }
        Application(left, right) => Application(
            Box::new(substitute(left, target_name, arg)),
            Box::new(substitute(right, target_name, arg)),
        ),
        // the domain is evaluated in the outer scope, so it always gets
        // substituted, but `var_name` shadows `target_name` inside
        // `codomain`/the body from here on, exactly like `Let`'s `scope`
        // below - leaving it be avoids incorrectly substituting through an
        // inner binder that happens to reuse the same name (eg. two nested
        // `\lambda n: Nat. ...` using `n` for unrelated variables)
        Abstraction(var_name, domain, codomain) => Abstraction(
            var_name.to_string(),
            Box::new(substitute(domain, target_name, arg)),
            if var_name != target_name {
                Box::new(substitute(codomain, target_name, arg))
            } else {
                codomain.clone()
            },
        ),
        Product(var_name, domain, codomain) => Product(
            var_name.to_string(),
            Box::new(substitute(domain, target_name, arg)),
            if var_name != target_name {
                Box::new(substitute(codomain, target_name, arg))
            } else {
                codomain.clone()
            },
        ),
        Let(var_name, var_type, body, scope) => {
            let var_type = if var_type.is_some() {
                Some(substitute(
                    &(**var_type).as_ref().unwrap(),
                    target_name,
                    arg,
                ))
            } else {
                None
            };
            let body = substitute(body, target_name, arg);
            // the name is overridden in `body`'s scope
            let scope = if var_name != target_name {
                substitute(scope, target_name, arg)
            } else {
                (**scope).to_owned()
            };

            Let(
                var_name.to_string(),
                Box::new(var_type),
                Box::new(body),
                Box::new(scope),
            )
        }
        Match(matched_term, branches) => Match(
            Box::new(substitute(matched_term, target_name, arg)),
            //TODO i dont want to clone branches here tbh
            simple_map(branches.clone(), |(pattern, body)| {
                (
                    substitute(&pattern, target_name, arg),
                    substitute(&body, target_name, arg),
                )
            }),
        ),
        //TODO implementare qua la sostituzione delle metavariabili?
        Meta(_) => term.clone(),
    }
}

/// Applies every mapping of a unification `substitution` to `term`. Keys are
/// tagged by `is_substitutable` (see `unification.rs`) as either
/// `metavariable_<idx>` (a `?`-introduced inference variable, applied via
/// `substitute_meta`) or `variable_<name>` (a plain, non-constant bound
/// variable unification solved for by name - eg. a parametrized inductive
/// constructor's own type parameter - applied via `substitute`).
pub fn apply_substitution(
    term: &CicTerm,
    substitution: &Substitution<CicTerm>,
) -> CicTerm {
    let mut result = term.to_owned();
    for key in substitution.names() {
        let value = substitution.get(key).expect("key came from `names()`");
        if let Some(meta_idx) = key.strip_prefix("metavariable_") {
            result = substitute_meta(
                &result,
                &meta_idx.parse().expect("metavariable_ key isn't an index"),
                value,
            );
        } else if let Some(var_name) = key.strip_prefix("variable_") {
            result = substitute(&result, var_name, value);
        }
    }
    result
}

/// Creates the CIC type of a function with named arguments `arg_types`
/// that returns a value of type `base`
pub fn make_multiarg_fun_type(
    arg_types: &[(String, CicTerm)],
    base: &CicTerm,
) -> CicTerm {
    generic_multiarg_fun_type::<Cic, _>(
        arg_types,
        base,
        |arg_name, arg_type, sub_type| {
            CicTerm::Product(arg_name, Box::new(arg_type), Box::new(sub_type))
        },
    )
}

/// Given a term, it enumerates variables with De Bruijn indexes properly
pub fn index_variables(term: &CicTerm) -> CicTerm {
    fn solver(
        term: &CicTerm,
        current_dbi: i32,
        //TODO this doesnt support shadowing of already defined names
        bound_vars: &mut HashMap<String, i32>,
    ) -> CicTerm {
        match term {
            Sort(_) => term.to_owned(),
            Meta(_) => term.to_owned(),
            Variable(name, _) => match bound_vars.get(name) {
                Some(dbi) => Variable(name.to_string(), *dbi),
                // unbound variables in the term get the global variable index
                None => Variable(name.to_string(), GLOBAL_INDEX),
            },
            Abstraction(var_name, var_type, body) => {
                bound_vars.insert(var_name.to_string(), current_dbi);

                Abstraction(
                    var_name.to_string(),
                    Box::new(solver(var_type, current_dbi + 1, bound_vars)),
                    Box::new(solver(body, current_dbi + 1, bound_vars)),
                )
            }
            Product(var_name, var_type, body) => {
                bound_vars.insert(var_name.to_string(), current_dbi);

                Product(
                    var_name.to_string(),
                    Box::new(solver(var_type, current_dbi + 1, bound_vars)),
                    Box::new(solver(body, current_dbi + 1, bound_vars)),
                )
            }
            Let(var_name, var_type, body, scope) => {
                bound_vars.insert(var_name.to_string(), current_dbi);
                let var_type = if var_type.is_some() {
                    Some(solver(
                        &(**var_type).as_ref().unwrap(),
                        current_dbi + 1,
                        bound_vars,
                    ))
                } else {
                    None
                };

                Let(
                    var_name.to_string(),
                    Box::new(var_type),
                    Box::new(solver(body, current_dbi + 1, bound_vars)),
                    Box::new(solver(scope, current_dbi + 1, bound_vars)),
                )
            }
            Application(left, right) => Application(
                Box::new(solver(left, current_dbi, bound_vars)),
                Box::new(solver(right, current_dbi, bound_vars)),
            ),
            Match(matched_term, branches) => {
                let matched_term =
                    solver(matched_term, current_dbi, bound_vars);
                // TODO reimplement this
                // this code needs to distinguish between type argument (terms)
                // and constructor argument (variables)
                // each pattern creates binding for each constructor argument
                // after this body does the same thing starting from the last index
                // used in the pattern

                Match(Box::new(matched_term), branches.to_owned())
            }
        }
    }

    solver(term, FIRST_INDEX, &mut HashMap::new())
}

/// Returns `term` where every occurance of `var_name` as a variable
/// is replaced as a constant
pub fn mark_as_constant(term: CicTerm, var_name: &str) -> CicTerm {
    substitute(
        &term,
        var_name,
        &Variable(var_name.to_string(), GLOBAL_INDEX),
    )
}
//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::type_theory::cic::{
        cic::{
            CicTerm::{Abstraction, Sort, Variable},
            GLOBAL_INDEX, PLACEHOLDER_DBI,
        },
        cic_utils::{index_variables, substitute, swap_proof_hole},
    };

    #[test]
    fn test_substitute_does_not_cross_a_shadowing_binder() {
        // Regression test: substituting `n` into a term that itself contains
        // an inner binder rebinding the name `n` (eg. a lambda literal
        // passed as an argument to a function whose own body already uses
        // `n` for something else, as in `apply_twice(\lambda n: Nat. s(n),
        // z)` where `apply_twice`'s own signature is `(f: Nat -> Nat, n:
        // Nat)`) must leave that inner binder's body untouched: the `n`
        // inside it refers to the inner binder, not the outer one being
        // substituted.
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let s = Variable("s".to_string(), GLOBAL_INDEX);
        let z = Variable("z".to_string(), GLOBAL_INDEX);

        // \lambda n: Nat. s(n) -- an inner binder reusing the name `n`
        let inner_lambda = Abstraction(
            "n".to_string(),
            Box::new(nat.clone()),
            Box::new(crate::type_theory::cic::cic::CicTerm::Application(
                Box::new(s.clone()),
                Box::new(Variable("n".to_string(), 0)),
            )),
        );

        // substituting the *outer* `n` with `z` must not reach inside
        // `inner_lambda`'s own body, since its own `n` shadows the outer one
        assert_eq!(
            substitute(&inner_lambda, "n", &z),
            inner_lambda,
            "substitute must not descend into a nested binder that shadows the substituted name"
        );

        // the domain (type) position isn't shadowed by the binder it
        // belongs to, so it must still be substituted
        let shadowing_in_domain = Abstraction(
            "n".to_string(),
            Box::new(Variable("n".to_string(), GLOBAL_INDEX)),
            Box::new(nat.clone()),
        );
        assert_eq!(
            substitute(&shadowing_in_domain, "n", &z),
            Abstraction("n".to_string(), Box::new(z.clone()), Box::new(nat.clone())),
            "substitute must still apply to a binder's own domain type"
        );

        // an outer occurrence of `n` (not shadowed) is still substituted
        let outer_application = crate::type_theory::cic::cic::CicTerm::Application(
            Box::new(inner_lambda.clone()),
            Box::new(Variable("n".to_string(), GLOBAL_INDEX)),
        );
        assert_eq!(
            substitute(&outer_application, "n", &z),
            crate::type_theory::cic::cic::CicTerm::Application(
                Box::new(inner_lambda),
                Box::new(z),
            ),
            "substitute must still replace a genuinely free/outer occurrence of the name"
        );
    }

    #[test]
    fn test_swap_proof_hole_preserves_abstraction_shape() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let hole = Sort("THIS_IS_A_PARTIAL_PROOF_HOLE".to_string());
        let outer_abstraction = Abstraction(
            "n".to_string(),
            Box::new(nat.clone()),
            Box::new(hole.clone()),
        );

        assert_eq!(
            swap_proof_hole(&outer_abstraction, &nat),
            Abstraction(
                "n".to_string(),
                Box::new(nat.clone()),
                Box::new(nat.clone())
            ),
            "swap_proof_hole must rebuild a single Abstraction as an Abstraction"
        );

        // nested case, as produced by two successive `intro` calls
        let inner_abstraction = Abstraction(
            "m".to_string(),
            Box::new(nat.clone()),
            Box::new(hole.clone()),
        );
        let nested = Abstraction(
            "n".to_string(),
            Box::new(nat.clone()),
            Box::new(inner_abstraction.clone()),
        );

        assert_eq!(
            swap_proof_hole(&nested, &nat),
            Abstraction(
                "n".to_string(),
                Box::new(nat.clone()),
                Box::new(Abstraction(
                    "m".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                )),
            ),
            "swap_proof_hole must preserve Abstraction shape through nested expressions"
        );
    }

    #[test]
    fn test_index_variables() {
        assert_eq!(
            index_variables(&Variable("x".to_string(), PLACEHOLDER_DBI)),
            Variable("x".to_string(), GLOBAL_INDEX),
            "Variable indexer doesnt use the global index properly"
        );

        assert_eq!(
            index_variables(&Abstraction(
                "y".to_string(),
                Box::new(Sort("TYPE".to_string())),
                Box::new(Variable("y".to_string(), PLACEHOLDER_DBI)),
            )),
            Abstraction(
                "y".to_string(),
                Box::new(Sort("TYPE".to_string())),
                Box::new(Variable("y".to_string(), 0)),
            ),
            "Abstraction indexing not working"
        );

        assert_eq!(
            index_variables(&Abstraction(
                "a".to_string(),
                Box::new(Variable("Unit".to_string(), PLACEHOLDER_DBI)),
                Box::new(Abstraction(
                    "b".to_string(),
                    Box::new(Sort("TYPE".to_string())),
                    Box::new(Variable("b".to_string(), PLACEHOLDER_DBI)),
                )),
            )),
            Abstraction(
                "a".to_string(),
                Box::new(Variable("Unit".to_string(), GLOBAL_INDEX)),
                Box::new(Abstraction(
                    "b".to_string(),
                    Box::new(Sort("TYPE".to_string())),
                    Box::new(Variable("b".to_string(), 1)),
                )),
            )
        );

        // // Test 4: Application with variables
        // let app = Application(
        //     Box::new(Abstraction(
        //         "f".to_string(),
        //         Box::new(Sort("TYPE".to_string())),
        //         Box::new(Variable("x".to_string(), 0)),
        //     )),
        //     Box::new(Variable("y".to_string(), 0)),
        // );
        // let expected_app = Application(
        //     Box::new(Abstraction(
        //         "f".to_string(),
        //         Box::new(Sort("TYPE".to_string())),
        //         Box::new(Variable("x".to_string(), 1)),
        //     )),
        //     Box::new(Variable("y".to_string(), 0)),
        // );
        // assert_eq!(index_variables(&app), expected_app);

        // // Test 5: Product with variables
        // let prod = Product(
        //     "f".to_string(),
        //     Box::new(Sort("TYPE".to_string())),
        //     Box::new(Abstraction(
        //         "x".to_string(),
        //         Box::new(Sort("TYPE".to_string())),
        //         Box::new(Variable("y".to_string(), 0)),
        //     )),
        // );
        // let expected_prod = Product(
        //     "f".to_string(),
        //     Box::new(Sort("TYPE".to_string())),
        //     Box::new(Abstraction(
        //         "x".to_string(),
        //         Box::new(Sort("TYPE".to_string())),
        //         Box::new(Variable("y".to_string(), 2)),
        //     )),
        // );
        // assert_eq!(index_variables(&prod), expected_prod);

        // Test 6: Match with variables
        // let match_term = Match(
        //     Box::new(Variable("x".to_string(), 0)),
        //     vec![
        //         vec![Variable("y".to_string(), 0)],
        //         vec![Variable("z".to_string(), 0)],
        //     ],
        // );
        // let expected_match = Match(
        //     Box::new(Variable("x".to_string(), 0)),
        //     vec![
        //         vec![Variable("y".to_string(), 1)],
        //         vec![Variable("z".to_string(), 2)],
        //     ],
        // );
        // assert_eq!(index_variables(&match_term), expected_match);
    }

    // #[test]
    // fn test_delta_reduce() {
    //     // Test delta reduction for variables
    //     let env = Environment::default_environment();
    //     let var = Variable("x".to_string(), 0);
    //     match delta_reduce(&env, var) {
    //         Err(e) => assert_eq!(e, "Variable x is not present in Δ so it doesnt have a substitution"),
    //         Ok(_) => panic!("Expected error for undefined variable"),
    //     }

    //     // Add a substitution and test again
    //     env.add_substitution("x", &Variable("y".to_string(), 0));
    //     match delta_reduce(&env, var) {
    //         Err(e) => panic!("Expected success but got error: {}", e),
    //         Ok(reduced) => assert_eq!(reduced, Variable("y".to_string(), 0)),
    //     }
    // }

    // #[test]
    // fn test_term_formatter() {
    //     // Test formatting for different term types
    //     let sort = Sort("TYPE".to_string());
    //     let var = Variable("x".to_string(), 0);
    //     let abs = Abstraction("f".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("x".to_string(), 0)));
    //     let app = Application(Box::new(abs.clone()), Box::new(var.clone()));

    //     assert_eq!(format!("{}", sort), "TYPE");
    //     assert_eq!(format!("{}", var), "x");
    //     assert_eq!(format!("{}", abs), "λf:TYPE. x");
    //     assert_eq!(format!("{}", app), "(λf:TYPE. x x)");
    // }

    // #[test]
    // fn test_get_variables_as_terms() {
    //     // Test getting variables from a function type
    //     let fun_type = make_multiarg_fun_type(
    //         &[("x".to_string(), Sort("TYPE".to_string())), ("y".to_string(), Sort("PROP".to_string()))],
    //         &Sort("TYPE".to_string()),
    //     );
    //     assert_eq!(get_variables_as_terms(&fun_type), vec![Variable("x".to_string(), 0), Variable("y".to_string(), 1)]);
    // }

    // #[test]
    // fn test_get_arg_types() {
    //     // Test getting argument types from a function type
    //     let fun_type = make_multiarg_fun_type(
    //         &[("x".to_string(), Sort("TYPE".to_string())), ("y".to_string(), Sort("PROP".to_string()))],
    //         &Sort("TYPE".to_string()),
    //     );
    //     assert_eq!(get_arg_types(&fun_type), vec![Sort("TYPE".to_string()), Sort("PROP".to_string())]);
    // }

    // #[test]
    // fn test_apply_arguments() {
    //     // Test applying arguments to a function
    //     let fun = Abstraction("f".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("x".to_string(), 0)));
    //     let args = vec![Variable("y".to_string(), 0)];
    //     assert_eq!(apply_arguments(&fun, args), Application(Box::new(fun.clone()), Box::new(Variable("y".to_string(), 0))));
    // }

    // #[test]
    // fn test_clone_product_with_different_result() {
    //     // Test cloning a product with different result
    //     let prod = Product(
    //         "f".to_string(),
    //         Box::new(Sort("TYPE".to_string())),
    //         Box::new(Abstraction("x".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("y".to_string(), 0))))
    //     );
    //     let new_result = Variable("z".to_string(), 0);
    //     assert_eq!(
    //         clone_product_with_different_result(&prod, new_result),
    //         Product(
    //             "f".to_string(),
    //             Box::new(Sort("TYPE".to_string())),
    //             Box::new(Abstraction("x".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(new_result.clone())))
    //         )
    //     );
    // }

    // #[test]
    // fn test_get_prod_innermost() {
    //     // Test getting the innermost body of a product
    //     let prod = Product(
    //         "f".to_string(),
    //         Box::new(Sort("TYPE".to_string())),
    //         Box::new(Product("g".to_string(), Box::new(Sort("PROP".to_string())), Box::new(Variable("x".to_string(), 0))))
    //     );
    //     assert_eq!(get_prod_innermost(&prod), &Variable("x".to_string(), 0));
    // }

    // #[test]
    // fn test_application_args() {
    //     // Test getting arguments from an application
    //     let app = Application(
    //         Box::new(Abstraction("f".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("x".to_string(), 0))),
    //         Box::new(Variable("y".to_string(), 0))
    //     );
    //     assert_eq!(application_args(app), vec![Variable("y".to_string(), 0)]);
    // }

    // #[test]
    // fn test_get_applied_function() {
    //     // Test getting the applied function from an application
    //     let app = Application(
    //         Box::new(Abstraction("f".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("x".to_string(), 0))),
    //         Box::new(Variable("y".to_string(), 0))
    //     );
    //     assert_eq!(get_applied_function(&app), Abstraction("f".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("x".to_string(), 0))));
    // }

    // #[test]
    // fn test_is_instance_of() {
    //     // Test checking if a term is an instance of a type
    //     let var = Variable("Nat".to_string(), 0);
    //     assert!(is_instance_of(&var, "Nat"));
    //     assert!(!is_instance_of(&var, "Bool"));
    // }

    // #[test]
    // fn test_references() {
    //     // Test checking if a term references a variable
    //     let app = Application(
    //         Box::new(Abstraction("f".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("x".to_string(), 0))),
    //         Box::new(Variable("y".to_string(), 0))
    //     );
    //     assert!(references(&app, "x"));
    //     assert!(!references(&app, "z"));
    // }

    // #[test]
    // fn test_check_positivity() {
    //     // Test checking positivity of a variable in a function type
    //     let fun_type = make_multiarg_fun_type(
    //         &[],
    //         &Sort("TYPE".to_string()),
    //     );
    //     assert!(check_positivity(&fun_type, "x"));
    // }

    // #[test]
    // fn test_substitute_meta() {
    //     // Test substituting a meta variable
    //     let term = Meta(0);
    //     let arg = Variable("x".to_string(), 0);
    //     assert_eq!(substitute_meta(&term, &0, &arg), arg.clone());
    //     assert_ne!(substitute_meta(&term, &1, &arg), arg);
    // }

    // #[test]
    // fn test_substitute() {
    //     // Test substituting a variable
    //     let term = Variable("x".to_string(), 0);
    //     let arg = Variable("y".to_string(), 0);
    //     assert_eq!(substitute(&term, "x", &arg), arg.clone());
    //     assert_ne!(substitute(&term, "z", &arg), arg);
    // }

    // #[test]
    // fn test_make_multiarg_fun_type() {
    //     // Test creating a multi-argument function type
    //     let fun_type = make_multiarg_fun_type(
    //         &[("x".to_string(), Sort("TYPE".to_string())), ("y".to_string(), Sort("PROP".to_string()))],
    //         &Sort("TYPE".to_string()),
    //     );
    //     assert_eq!(fun_type, Product("x", Box::new(Sort("TYPE".to_string())), Box::new(Product("y", Box::new(Sort("PROP".to_string())), Box::new(Sort("TYPE".to_string()))))));
    // }

    // #[test]
    // fn test_eta_expand() {
    //     // Test eta expansion
    //     let body = Variable("x".to_string(), 0);
    //     let args = vec![("y".to_string(), Sort("TYPE".to_string()))];
    //     assert_eq!(
    //         eta_expand(&args, &body),
    //         Abstraction("y", Box::new(Sort("TYPE".to_string())), Box::new(body.clone()))
    //     );
    // }

    // #[test]
    // fn test_index_variables() {
    //     // Test index variables function
    //     let var = Variable("x".to_string(), 0);
    //     assert_eq!(index_variables(&var), var);

    //     let abs = Abstraction("y".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("z".to_string(), 0)));
    //     let expected_abs = Abstraction("y".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("z".to_string(), 1)));
    //     assert_eq!(index_variables(&abs), expected_abs);

    //     let nested_abs = Abstraction(
    //         "a".to_string(),
    //         Box::new(Abstraction("b".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("c".to_string(), 0)))),
    //         Box::new(Variable("d".to_string(), 0))
    //     );
    //     let expected_nested_abs = Abstraction(
    //         "a".to_string(),
    //         Box::new(Abstraction("b".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("c".to_string(), 2)))),
    //         Box::new(Variable("d".to_string(), 1))
    //     );
    //     assert_eq!(index_variables(&nested_abs), expected_nested_abs);

    //     let app = Application(
    //         Box::new(Abstraction("f".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("x".to_string(), 0)))),
    //         Box::new(Variable("y".to_string(), 0))
    //     );
    //     let expected_app = Application(
    //         Box::new(Abstraction("f".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("x".to_string(), 1)))),
    //         Box::new(Variable("y".to_string(), 0))
    //     );
    //     assert_eq!(index_variables(&app), expected_app);

    //     let prod = Product(
    //         "f".to_string(),
    //         Box::new(Sort("TYPE".to_string())),
    //         Box::new(Abstraction("x".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("y".to_string(), 0))))
    //     );
    //     let expected_prod = Product(
    //         "f".to_string(),
    //         Box::new(Sort("TYPE".to_string())),
    //         Box::new(Abstraction("x".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("y".to_string(), 2))))
    //     );
    //     assert_eq!(index_variables(&prod), expected_prod);

    //     let match_term = Match(
    //         Box::new(Variable("x".to_string(), 0)),
    //         vec![vec![Variable("y".to_string(), 0)], vec![Variable("z".to_string(), 0)]]
    //     );
    //     let expected_match = Match(
    //         Box::new(Variable("x".to_string(), 0)),
    //         vec![vec![Variable("y".to_string(), 1)], vec![Variable("z".to_string(), 2)]]
    //     );
    //     assert_eq!(index_variables(&match_term), expected_match);
    // }
}
