use super::{
    fof::{Symbols, INDIVIDUAL_SORT},
    syntax::{atomic_type, atomic_word, sym},
};
use crate::{
    error::LofError,
    parser::api::PResult,
    type_theory::{
        environment::Environment,
        fol::{fol::Fol, fol_utils::make_multiarg_fun_type},
        grammars::fol::FolFormula::{self, Predicate},
        interface::TypeTheory,
    },
};
use nom::{
    branch::alt,
    combinator::map,
    multi::separated_list1,
    sequence::{delimited, pair, preceded},
};
use std::collections::{HashMap, HashSet};

/// The type of sorts, `nat: $tType` declares the sort `nat`
pub const TYPE_OF_TYPES: &str = "$tType";
/// The type of formulas, the result type of predicates
pub const BOOLEAN_TYPE: &str = "$o";
/// Sorts every problem has without declaring them
const DEFINED_SORTS: [&str; 4] = [INDIVIDUAL_SORT, "$int", "$rat", "$real"];
/// Nullary predicates every problem has without declaring them
const DEFINED_PREDICATES: [&str; 2] = ["$true", "$false"];

#[derive(Debug, Clone, PartialEq)]
/// A TF0 `tff(name, type, ...)` declaration
pub enum TypeDeclaration {
    /// sort_name
    Sort(String),
    /// symbol_name, [arg_sorts], result_sort (`$o` for predicates)
    Symbol(String, Vec<String>, String),
}

//############################# PARSING

/// `sort` or `(sort1 * sort2 * ...)`
fn argument_types(input: &str) -> PResult<'_, Vec<String>> {
    alt((
        delimited(sym("("), separated_list1(sym("*"), atomic_type), sym(")")),
        map(atomic_type, |sort| vec![sort]),
    ))(input)
}

/// `<tff_top_level_type>` of TF0: an atomic type or a mapping type
/// `args > result`, possibly parenthesized. Returns ([arg_sorts], result_sort)
fn type_expression(input: &str) -> PResult<'_, (Vec<String>, String)> {
    if sym("!>")(input).is_ok() {
        return Err(nom::Err::Failure(LofError::unsupported(
            "Polymorphic TFF types (TF1) are not supported",
        )));
    }
    alt((
        pair(argument_types, preceded(sym(">"), atomic_type)),
        map(atomic_type, |sort| (vec![], sort)),
        delimited(sym("("), type_expression, sym(")")),
    ))(input)
}

fn declaration_body(input: &str) -> PResult<'_, TypeDeclaration> {
    let (input, name) = atomic_word(input)?;
    let (input, (args, result)) = preceded(sym(":"), type_expression)(input)?;

    let declaration = match (result.as_str(), args.is_empty()) {
        (TYPE_OF_TYPES, true) => TypeDeclaration::Sort(name),
        (TYPE_OF_TYPES, false) => {
            return Err(nom::Err::Failure(LofError::unsupported(format!(
                "Type constructor {} is not supported (TF1)",
                name
            ))))
        }
        _ => TypeDeclaration::Symbol(name, args, result),
    };
    Ok((input, declaration))
}

/// Parses the formula of a `tff(name, type, ...)` annotated formula
pub fn type_declaration(input: &str) -> PResult<'_, TypeDeclaration> {
    alt((
        delimited(sym("("), declaration_body, sym(")")),
        declaration_body,
    ))(input)
}

//############################# PARSING
//
//
//############################# SIGNATURE

fn sort_formula(sort: &str) -> FolFormula {
    Predicate(sort.to_string(), vec![])
}

/// Returns the sort of a numeric literal symbol, `None` for other symbols
fn literal_sort(name: &str) -> Option<&'static str> {
    let digits = name.trim_start_matches(['+', '-']);
    if !digits.starts_with(|c: char| c.is_ascii_digit()) {
        None
    } else if digits.contains('/') {
        Some("$rat")
    } else if digits.contains(['.', 'e', 'E']) {
        Some("$real")
    } else {
        Some("$int")
    }
}

/// Registers `name: args > result` in `environment`, following the FOL
/// conventions: predicates in the predicate store, functions and constants
/// in the context with their curried `Arrow` type
fn declare_symbol(
    environment: &mut Environment<Fol>,
    name: &str,
    args: &[String],
    result: &str,
) {
    if result == BOOLEAN_TYPE {
        let arg_types = args.iter().map(|arg| sort_formula(arg)).collect();
        environment.add_predicate(name, &arg_types);
    } else {
        let arg_types: Vec<_> = args
            .iter()
            .map(|arg| ("_".to_string(), sort_formula(arg)))
            .collect();
        let fun_type =
            make_multiarg_fun_type(&arg_types, &sort_formula(result));
        environment.add_to_context(name, &fun_type);
    }
}

fn unsupported_interpreted(name: &str) -> LofError {
    LofError::unsupported(format!(
        "Interpreted TPTP symbol {} is not supported",
        name
    ))
}

/// Builds the FOL typing environment of a problem out of its type
/// `declarations`. Sorts become nullary predicates, as in FOL, and symbols
/// among `used` that aren't declared get the TPTP default types: `$i` for
/// every argument and for the result of functions, numeric literals are
/// `$int`/`$rat`/`$real`
pub fn build_environment(
    declarations: &[TypeDeclaration],
    used: &Symbols,
) -> Result<Environment<Fol>, LofError> {
    let mut environment = Fol::default_environment();
    let mut errors = vec![];

    let mut sorts: HashSet<String> =
        DEFINED_SORTS.iter().map(|sort| sort.to_string()).collect();
    for declaration in declarations {
        if let TypeDeclaration::Sort(sort) = declaration {
            sorts.insert(sort.to_string());
        }
    }
    for sort in &sorts {
        environment.add_predicate(sort, &vec![]);
    }
    for predicate in DEFINED_PREDICATES {
        environment.add_predicate(predicate, &vec![]);
    }

    let mut declared: HashMap<&str, (&Vec<String>, &String)> = HashMap::new();
    for declaration in declarations {
        let TypeDeclaration::Symbol(name, args, result) = declaration else {
            continue;
        };

        let unknown_sorts: Vec<_> = args
            .iter()
            .chain([result])
            .filter(|sort| !sorts.contains(*sort) && *sort != BOOLEAN_TYPE)
            .collect();
        if !unknown_sorts.is_empty() {
            errors.extend(unknown_sorts.into_iter().map(|sort| {
                LofError::UnboundName {
                    kind: "sort",
                    name: sort.to_string(),
                }
            }));
            continue;
        }
        if args.contains(&BOOLEAN_TYPE.to_string()) {
            errors.push(LofError::unsupported(format!(
                "Symbol {} takes formulas as arguments (TXF is not supported)",
                name
            )));
            continue;
        }

        match declared.get(name.as_str()) {
            Some(previous) if *previous != (args, result) => {
                errors.push(LofError::custom(format!(
                    "Symbol {} is declared with conflicting types",
                    name
                )));
            }
            Some(_) => {}
            None => {
                declared.insert(name, (args, result));
                declare_symbol(&mut environment, name, args, result);
            }
        }
    }

    for (name, arity) in &used.functions {
        if declared.contains_key(name.as_str()) {
            continue;
        }
        if let Some(sort) = literal_sort(name) {
            environment.add_to_context(name, &sort_formula(sort));
        } else if name.starts_with('$') {
            errors.push(unsupported_interpreted(name));
        } else {
            let args = vec![INDIVIDUAL_SORT.to_string(); *arity];
            declare_symbol(&mut environment, name, &args, INDIVIDUAL_SORT);
        }
    }
    for (name, arity) in &used.predicates {
        if declared.contains_key(name.as_str())
            || DEFINED_PREDICATES.contains(&name.as_str())
        {
            continue;
        }
        if name.starts_with('$') {
            errors.push(unsupported_interpreted(name));
        } else {
            let args = vec![INDIVIDUAL_SORT.to_string(); *arity];
            declare_symbol(&mut environment, name, &args, BOOLEAN_TYPE);
        }
    }

    if errors.is_empty() {
        Ok(environment)
    } else {
        Err(LofError::aggregate(errors))
    }
}

//############################# SIGNATURE
