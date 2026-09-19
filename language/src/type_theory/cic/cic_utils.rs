use super::cic::CicTerm::{
    Abstraction, Application, Let, Match, Meta, Product, Sort, Variable,
};
use super::cic::{Cic, CicTerm};
use crate::misc::simple_map;
use crate::type_theory::cic::cic::{NameKind, PLACEHOLDER_DBI};
use crate::type_theory::cic::elaboration::index_variables_in_store;
use crate::type_theory::commons::utils::{
    generic_multiarg_fun_type, ElabStore,
};
use std::fmt;

fn term_formatter(term: &CicTerm, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match term {
        // (sort name)
        Sort(name) => write!(f, "{}", name),
        // (var name)
        Variable(name, NameKind::Const()) => {
            write!(f, "{}|G", name)
        }
        Variable(name, NameKind::Local()) => {
            write!(f, "{}|L", name)
        }
        Variable(name, NameKind::Bound(dbi)) => {
            let dbi_text = if *dbi == PLACEHOLDER_DBI {
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
                let mut result =
                    vec![Variable(var_name.to_owned(), NameKind::Bound(index))];
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

/// Clones the given `proof_term`, swapping the hole with the given `new_body`
pub fn swap_proof_hole(proof_term: &CicTerm, new_body: &CicTerm) -> CicTerm {
    match proof_term {
        Abstraction(var_name, var_type, body) => {
            let new_body = swap_proof_hole(body, new_body);
            Abstraction(
                var_name.to_owned(),
                var_type.clone(),
                Box::new(new_body),
            )
        }
        Sort(_) => new_body.to_owned(),
        Variable(_, _) => new_body.to_owned(),
        Application(_, _) => new_body.to_owned(),
        _ => panic!("TODO: handle better"),
    }
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
        Variable(_, NameKind::Const()) => true,
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

/// The binder names a match pattern introduces, depth first left to right:
/// every variable sitting in an argument position of the pattern's
/// constructor spine, at any nesting depth. Mirrors the rule the elaborator
/// uses when it extends a branch's scope, so a branch body's indices line up
/// with the telescope the pattern actually opened.
pub fn pattern_binder_names(pattern: &CicTerm) -> Vec<String> {
    match pattern {
        Application(_, _) => application_args(pattern)
            .iter()
            .flat_map(|arg| match arg {
                Variable(name, _) => vec![name.to_string()],
                Application(_, _) => pattern_binder_names(arg),
                _ => vec![],
            })
            .collect(),
        _ => vec![],
    }
}

/// How many binders a match pattern introduces for its branch
fn pattern_binder_count(pattern: &CicTerm) -> i32 {
    pattern_binder_names(pattern).len() as i32
}

/// Replaces every occurrence of the binder `body` is the body of with a
/// locally free reference called `name`, ie the `open` of a locally nameless
/// representation.
pub fn open_term(body: &CicTerm, name: &str) -> CicTerm {
    fn solver(term: &CicTerm, name: &str, depth: i32) -> CicTerm {
        match term {
            Sort(_) | Meta(_) => term.clone(),
            Variable(_, NameKind::Const()) | Variable(_, NameKind::Local()) => {
                term.clone()
            }
            Variable(var_name, NameKind::Bound(dbi)) => {
                if *dbi == depth {
                    // shi to open
                    Variable(name.to_string(), NameKind::Local())
                } else if *dbi > depth {
                    // refers past the binder being opened, and that binder is
                    // now gone from the telescope, so it moves one closer.
                    Variable(var_name.to_string(), NameKind::Bound(dbi - 1))
                } else {
                    // bound by a binder inside `term`, untouched
                    Variable(var_name.to_string(), NameKind::Bound(*dbi))
                }
            }
            Application(left, right) => Application(
                Box::new(solver(left, name, depth)),
                Box::new(solver(right, name, depth)),
            ),
            Abstraction(var_name, domain, codomain) => Abstraction(
                var_name.to_string(),
                Box::new(solver(domain, name, depth)),
                Box::new(solver(codomain, name, depth + 1)),
            ),
            Product(var_name, domain, codomain) => Product(
                var_name.to_string(),
                Box::new(solver(domain, name, depth)),
                Box::new(solver(codomain, name, depth + 1)),
            ),
            Let(var_name, var_type, definition, scope) => Let(
                var_name.to_string(),
                Box::new(
                    (**var_type).as_ref().map(|t| solver(t, name, depth + 1)),
                ),
                Box::new(solver(definition, name, depth)),
                Box::new(solver(scope, name, depth + 1)),
            ),
            Match(matched_term, branches) => Match(
                Box::new(solver(matched_term, name, depth)),
                simple_map(branches.clone(), |(pattern, branch_body)| {
                    // a pattern opens one binder per variable it introduces,
                    // and the branch was elaborated under all of them
                    let inner = depth + pattern_binder_count(&pattern);
                    (
                        solver(&pattern, name, inner),
                        solver(&branch_body, name, inner),
                    )
                }),
            ),
        }
    }

    solver(body, name, 0)
}

/// Inverse of `open_term`: turns the locally free `name` back into the De
/// Bruijn index of the binder being rebuilt around `body`.
pub fn close_term(body: &CicTerm, name: &str) -> CicTerm {
    fn solver(term: &CicTerm, name: &str, depth: i32) -> CicTerm {
        match term {
            Sort(_) | Meta(_) => term.clone(),
            Variable(_, NameKind::Const()) => term.clone(),
            Variable(var_name, NameKind::Bound(dbi)) => {
                if *dbi >= depth {
                    // a binder is being put back in front of it
                    Variable(var_name.to_string(), NameKind::Bound(dbi + 1))
                } else {
                    term.clone()
                }
            }
            Variable(var_name, NameKind::Local()) => {
                if var_name == name {
                    Variable(var_name.to_string(), NameKind::Bound(depth))
                } else {
                    term.clone()
                }
            }
            Application(left, right) => Application(
                Box::new(solver(left, name, depth)),
                Box::new(solver(right, name, depth)),
            ),
            Abstraction(var_name, domain, codomain) => Abstraction(
                var_name.to_string(),
                Box::new(solver(domain, name, depth)),
                Box::new(solver(codomain, name, depth + 1)),
            ),
            Product(var_name, domain, codomain) => Product(
                var_name.to_string(),
                Box::new(solver(domain, name, depth)),
                Box::new(solver(codomain, name, depth + 1)),
            ),
            Let(var_name, var_type, definition, scope) => Let(
                var_name.to_string(),
                Box::new(
                    (**var_type).as_ref().map(|t| solver(t, name, depth + 1)),
                ),
                Box::new(solver(definition, name, depth)),
                Box::new(solver(scope, name, depth + 1)),
            ),
            Match(matched_term, branches) => Match(
                Box::new(solver(matched_term, name, depth)),
                simple_map(branches.clone(), |(pattern, branch_body)| {
                    let inner = depth + pattern_binder_count(&pattern);
                    (
                        solver(&pattern, name, inner),
                        solver(&branch_body, name, inner),
                    )
                }),
            ),
        }
    }

    solver(body, name, 0)
}

/// Given a `term` and a variable, returns a term where each instance of
/// `var_name` is substituted with `arg`
pub fn substitute(term: &CicTerm, target_name: &str, arg: &CicTerm) -> CicTerm {
    // TODO: this is meant to be a plain name-based rewrite with no index
    // bookkeeping
    substitute_base(term, target_name, arg)
}
/// `substitute` + also shifts indeces if binders are removed
pub fn substitute_and_lift(
    term: &CicTerm,
    target_name: &str,
    arg: &CicTerm,
) -> CicTerm {
    substitute_base(term, target_name, arg)
}

fn substitute_base(
    term: &CicTerm,
    target_name: &str,
    arg: &CicTerm,
) -> CicTerm {
    /// Increases every free `Bound` index in `term` by `amount` — "free" meaning
    /// it refers past `term`'s own binders, tracked via `cutoff`. Needed
    /// whenever a substituted argument is spliced back in `amount` binders
    /// deeper than where it was originally computed, so its own escaping
    /// references keep pointing to the same external things instead of being
    /// captured by binders they were just moved underneath.
    fn shift(term: &CicTerm, amount: i32) -> CicTerm {
        fn solver(term: &CicTerm, amount: i32, cutoff: i32) -> CicTerm {
            match term {
                Sort(_) => term.clone(),
                Meta(_) => term.clone(),
                // a `Local` names a context entry rather than a position,
                // so no amount of extra enclosing binders can change it --
                // this is exactly the property `open` buys us.
                Variable(_, NameKind::Local()) => term.clone(),
                Variable(_, NameKind::Const()) => term.clone(),
                Variable(var_name, NameKind::Bound(dbi)) => {
                    if *dbi >= cutoff {
                        Variable(
                            var_name.to_string(),
                            NameKind::Bound(dbi + amount),
                        )
                    } else {
                        term.clone()
                    }
                }
                Application(left, right) => Application(
                    Box::new(solver(left, amount, cutoff)),
                    Box::new(solver(right, amount, cutoff)),
                ),
                Abstraction(var_name, domain, codomain) => Abstraction(
                    var_name.to_string(),
                    Box::new(solver(domain, amount, cutoff)),
                    Box::new(solver(codomain, amount, cutoff + 1)),
                ),
                Product(var_name, domain, codomain) => Product(
                    var_name.to_string(),
                    Box::new(solver(domain, amount, cutoff)),
                    Box::new(solver(codomain, amount, cutoff + 1)),
                ),
                Let(var_name, var_type, body, scope) => Let(
                    var_name.to_string(),
                    Box::new(
                        (**var_type)
                            .as_ref()
                            .map(|t| solver(t, amount, cutoff + 1)),
                    ),
                    Box::new(solver(body, amount, cutoff)),
                    Box::new(solver(scope, amount, cutoff + 1)),
                ),
                Match(matched_term, branches) => Match(
                    Box::new(solver(matched_term, amount, cutoff)),
                    simple_map(branches.clone(), |(pattern, body)| {
                        // the branch sits under one binder per pattern
                        // variable, exactly as the elaborator numbered it
                        let inner = cutoff + pattern_binder_count(&pattern);
                        (
                            solver(&pattern, amount, inner),
                            solver(&body, amount, inner),
                        )
                    }),
                ),
            }
        }

        if amount == 0 {
            term.clone()
        } else {
            solver(term, amount, 0)
        }
    }

    // `depth` is how many binders we've descended through since the start
    // of this substitution: a `Bound` reference exactly at `depth` is the
    // one being removed (it gets `arg`, shifted so its own escaping
    // references still point outside correctly); one further out
    // (`dbi > depth`) has lost a binder and must be decremented; one more
    // local (`dbi < depth`, e.g. bound by a nested binder of the same
    // name) refers to something else entirely and is left alone. This is
    // what lets shadowing "just work" without a separate name-based check.
    fn solver(
        term: &CicTerm,
        target_name: &str,
        arg: &CicTerm,
        depth: i32,
    ) -> CicTerm {
        match term {
            Sort(_) => term.clone(),
            Meta(_) => term.clone(),
            // both consts and locally free vars are treated irreduceable
            Variable(_, NameKind::Const()) => term.clone(),
            Variable(_, NameKind::Local()) => term.clone(),
            Variable(var_name, NameKind::Bound(dbi)) => {
                if var_name == target_name && *dbi == depth {
                    shift(arg, depth)
                    // arg.clone()
                } else if *dbi > depth {
                    Variable(var_name.to_string(), NameKind::Bound(dbi - 1))
                } else {
                    term.clone()
                }
            }
            Application(left, right) => Application(
                Box::new(solver(left, target_name, arg, depth)),
                Box::new(solver(right, target_name, arg, depth)),
            ),
            Abstraction(var_name, domain, codomain) => Abstraction(
                var_name.to_string(),
                Box::new(solver(domain, target_name, arg, depth)),
                Box::new(solver(codomain, target_name, arg, depth + 1)),
            ),
            Product(var_name, domain, codomain) => Product(
                var_name.to_string(),
                Box::new(solver(domain, target_name, arg, depth)),
                Box::new(solver(codomain, target_name, arg, depth + 1)),
            ),
            Let(var_name, var_type, body, scope) => {
                let var_type = (**var_type)
                    .as_ref()
                    .map(|t| solver(t, target_name, arg, depth + 1));
                let body = solver(body, target_name, arg, depth);
                let scope = solver(scope, target_name, arg, depth + 1);

                Let(
                    var_name.to_string(),
                    Box::new(var_type),
                    Box::new(body),
                    Box::new(scope),
                )
            }
            Match(matched_term, branches) => Match(
                Box::new(solver(matched_term, target_name, arg, depth)),
                //TODO i dont want to clone branches here tbh
                simple_map(branches.clone(), |(pattern, body)| {
                    // the branch sits under one binder per pattern variable,
                    // exactly as the elaborator numbered it
                    let inner = depth + pattern_binder_count(&pattern);
                    (
                        solver(&pattern, target_name, arg, inner),
                        solver(&body, target_name, arg, inner),
                    )
                }),
            ),
        }
    }

    solver(term, target_name, arg, 0)
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
    index_variables_in_store(term, &ElabStore::empty())
}

/// Returns `term` where every occurance of `var_name` as a variable
/// is replaced as a constant
pub fn mark_as_constant(term: CicTerm, var_name: &str) -> CicTerm {
    substitute(
        &term,
        var_name,
        &Variable(var_name.to_string(), NameKind::Const()),
    )
}
//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::type_theory::cic::{
        cic::{
            CicTerm::{Abstraction, Application, Match, Sort, Variable},
            NameKind, PLACEHOLDER_DBI,
        },
        cic_utils::{index_variables, swap_proof_hole},
    };

    fn placeholder(name: &str) -> crate::type_theory::cic::cic::CicTerm {
        Variable(name.to_string(), NameKind::Bound(PLACEHOLDER_DBI))
    }
    fn free(name: &str) -> crate::type_theory::cic::cic::CicTerm {
        Variable(name.to_string(), NameKind::Const())
    }
    fn bound(name: &str, dbi: i32) -> crate::type_theory::cic::cic::CicTerm {
        Variable(name.to_string(), NameKind::Bound(dbi))
    }

    #[test]
    fn test_open_close_roundtrip_on_a_telescope_body() {
        use crate::type_theory::cic::cic::CicTerm::{Application, Product};
        use crate::type_theory::cic::cic_utils::{close_term, open_term};

        // body of `Π T:TYPE. Π P:(T -> PROP). <here>`, exactly the shape of
        // the `Exists` constructor: T sits at index 1, P at index 0, and both
        // get deeper as the body nests
        let body = Product(
            "t".to_string(),
            Box::new(Variable("T".to_string(), NameKind::Bound(1))),
            Box::new(Product(
                "_".to_string(),
                Box::new(Application(
                    Box::new(Variable("P".to_string(), NameKind::Bound(1))),
                    Box::new(Variable("t".to_string(), NameKind::Bound(0))),
                )),
                Box::new(Application(
                    Box::new(Variable("T".to_string(), NameKind::Bound(3))),
                    Box::new(Variable("P".to_string(), NameKind::Bound(2))),
                )),
            )),
        );

        // opening innermost first peels the whole telescope
        let opened = open_term(&open_term(&body, "P"), "T");
        let expected_opened = Product(
            "t".to_string(),
            Box::new(Variable("T".to_string(), NameKind::Local())),
            Box::new(Product(
                "_".to_string(),
                Box::new(Application(
                    Box::new(Variable("P".to_string(), NameKind::Local())),
                    Box::new(Variable("t".to_string(), NameKind::Bound(0))),
                )),
                Box::new(Application(
                    Box::new(Variable("T".to_string(), NameKind::Local())),
                    Box::new(Variable("P".to_string(), NameKind::Local())),
                )),
            )),
        );
        assert_eq!(
            opened, expected_opened,
            "open must turn every reference to a telescope binder into a \
             depth invariant Local, whatever depth it occurs at, and leave \
             the binders internal to the body (`t`) alone"
        );

        // and closing in the mirror order must give back exactly the original
        assert_eq!(
            close_term(&close_term(&opened, "T"), "P"),
            body,
            "close must be the inverse of open"
        );
    }

    #[test]
    fn test_swap_proof_hole_preserves_abstraction_shape() {
        let nat = Variable("Nat".to_string(), NameKind::Const());
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
            index_variables(&Variable(
                "x".to_string(),
                NameKind::Bound(PLACEHOLDER_DBI)
            )),
            Variable("x".to_string(), NameKind::Const()),
            "Variable indexer doesnt use the global index properly"
        );

        assert_eq!(
            index_variables(&Abstraction(
                "y".to_string(),
                Box::new(Sort("TYPE".to_string())),
                Box::new(Variable(
                    "y".to_string(),
                    NameKind::Bound(PLACEHOLDER_DBI)
                )),
            )),
            Abstraction(
                "y".to_string(),
                Box::new(Sort("TYPE".to_string())),
                Box::new(Variable("y".to_string(), NameKind::Bound(0))),
            ),
            "Abstraction indexing not working"
        );

        assert_eq!(
            index_variables(&Abstraction(
                "a".to_string(),
                Box::new(Variable(
                    "Unit".to_string(),
                    NameKind::Bound(PLACEHOLDER_DBI)
                )),
                Box::new(Abstraction(
                    "b".to_string(),
                    Box::new(Sort("TYPE".to_string())),
                    Box::new(Variable(
                        "b".to_string(),
                        NameKind::Bound(PLACEHOLDER_DBI)
                    )),
                )),
            )),
            Abstraction(
                "a".to_string(),
                Box::new(Variable("Unit".to_string(), NameKind::Const())),
                Box::new(Abstraction(
                    "b".to_string(),
                    Box::new(Sort("TYPE".to_string())),
                    Box::new(Variable("b".to_string(), NameKind::Bound(0))),
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
    #[test]
    fn test_index_variables_binds_match_pattern_arguments() {
        // match t { o => s(o), s(n) => n }
        // `o` is a nullary constructor: a bare pattern binds nothing, so both
        // occurrences stay free. `n` sits in an argument position of `s`, so
        // it binds over the pattern *and* the branch body.
        let term = Match(
            Box::new(placeholder("t")),
            vec![
                (
                    placeholder("o"),
                    Application(
                        Box::new(placeholder("s")),
                        Box::new(placeholder("o")),
                    ),
                ),
                (
                    Application(
                        Box::new(placeholder("s")),
                        Box::new(placeholder("n")),
                    ),
                    placeholder("n"),
                ),
            ],
        );

        assert_eq!(
            index_variables(&term),
            Match(
                Box::new(free("t")),
                vec![
                    (
                        free("o"),
                        Application(Box::new(free("s")), Box::new(free("o"))),
                    ),
                    (
                        Application(
                            Box::new(free("s")),
                            Box::new(bound("n", 0)),
                        ),
                        bound("n", 0),
                    ),
                ],
            ),
            "match pattern arguments must be indexed as binders of their branch"
        );
    }

    #[test]
    fn test_index_variables_binds_nested_match_pattern_arguments() {
        // match t { cons(h, cons(h2, ll)) => h }
        // three binders, depth-first left-to-right: h is outermost so it gets
        // the highest index, ll is innermost so it gets 0.
        let pattern = Application(
            Box::new(Application(
                Box::new(placeholder("cons")),
                Box::new(placeholder("h")),
            )),
            Box::new(Application(
                Box::new(Application(
                    Box::new(placeholder("cons")),
                    Box::new(placeholder("h2")),
                )),
                Box::new(placeholder("ll")),
            )),
        );
        let term = Match(
            Box::new(placeholder("t")),
            vec![(pattern, placeholder("h"))],
        );

        assert_eq!(
            index_variables(&term),
            Match(
                Box::new(free("t")),
                vec![(
                    Application(
                        Box::new(Application(
                            Box::new(free("cons")),
                            Box::new(bound("h", 2)),
                        )),
                        Box::new(Application(
                            Box::new(Application(
                                Box::new(free("cons")),
                                Box::new(bound("h2", 1)),
                            )),
                            Box::new(bound("ll", 0)),
                        )),
                    ),
                    bound("h", 2),
                )],
            ),
            "nested pattern arguments must all bind, outermost getting the highest index"
        );
    }

    #[test]
    fn test_index_variables_match_binders_shadow_and_stack_on_outer_scope() {
        // \T. \l. match l { cons(T, h, ll) => T }
        // the pattern rebinds `T`, shadowing the abstraction's own `T`, and
        // references from the branch body must count the pattern's binders.
        let pattern = Application(
            Box::new(Application(
                Box::new(Application(
                    Box::new(placeholder("cons")),
                    Box::new(placeholder("T")),
                )),
                Box::new(placeholder("h")),
            )),
            Box::new(placeholder("ll")),
        );
        let term = Abstraction(
            "T".to_string(),
            Box::new(Sort("TYPE".to_string())),
            Box::new(Abstraction(
                "l".to_string(),
                Box::new(placeholder("T")),
                Box::new(Match(
                    Box::new(placeholder("l")),
                    vec![(pattern, placeholder("T"))],
                )),
            )),
        );

        let indexed = index_variables(&term);
        let branch_body = match &indexed {
            Abstraction(_, _, outer_body) => match &**outer_body {
                Abstraction(_, _, inner_body) => match &**inner_body {
                    Match(_, branches) => branches[0].1.clone(),
                    other => panic!("expected a Match, got {:?}", other),
                },
                other => panic!("expected an Abstraction, got {:?}", other),
            },
            other => panic!("expected an Abstraction, got {:?}", other),
        };

        // scope is [T, l, T, h, ll]: the pattern's own `T` shadows the
        // abstraction's, so the body resolves to it at distance 2
        assert_eq!(
            branch_body,
            bound("T", 2),
            "a pattern binder must shadow an outer binder of the same name"
        );
    }

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
