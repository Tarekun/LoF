use super::{
    fof::{binary_connective, BinaryConnective},
    syntax::{
        atomic_word, distinct_object, dollar_word, number, sym, upper_word,
    },
};
use crate::{
    error::LofError,
    parser::api::PResult,
    type_theory::{
        environment::Environment,
        f::f::{SystemF, TYPE_KIND},
        grammars::f::{
            FTerm::{
                self, Abstraction, Application, TypeAbstraction,
                TypeApplication, Variable,
            },
            FType::{self, Arrow, Atomic, Forall, MetaVariable},
        },
        interface::{Kernel, TypeTheory},
    },
};
use nom::{
    branch::alt,
    character::complete::{char, one_of},
    combinator::{map, not, opt},
    multi::{many0, separated_list1},
    sequence::{delimited, pair, preceded, terminated},
};

// Formulas are encoded Church style, as terms of type `$o`. Connectives,
// quantifiers and equality are constants of the HOL environment
pub const BOOLEAN_TYPE: &str = "$o";
pub const INDIVIDUAL_TYPE: &str = "$i";
pub const TRUE: &str = "$true";
pub const FALSE: &str = "$false";
pub const NOT: &str = "~";
pub const AND: &str = "&";
pub const OR: &str = "|";
pub const IMPLY: &str = "=>";
pub const IFF: &str = "<=>";
/// `= : ∀α:*. α → α → $o`
pub const EQUALS: &str = "=";
/// `!! : ∀α:*. (α → $o) → $o`, universal quantification of a predicate
pub const PI: &str = "!!";
/// `?? : ∀α:*. (α → $o) → $o`, existential quantification of a predicate
pub const SIGMA: &str = "??";
/// Name of the TPTP kind, mapped to the System F kind `*`
const TPTP_KIND: &str = "$tType";

/// Placeholder for the implicit type argument of a polymorphic constant,
/// filled by `elaborate` once the type of its first argument is known
const HOLE: &str = "?";

fn hole() -> FType {
    MetaVariable(HOLE.to_string())
}
fn is_hole(typee: &FType) -> bool {
    matches!(typee, MetaVariable(name) if name == HOLE)
}
fn kind() -> FType {
    Atomic(TYPE_KIND.to_string())
}
fn boolean() -> FType {
    Atomic(BOOLEAN_TYPE.to_string())
}
fn arrow(domain: FType, codomain: FType) -> FType {
    Arrow(Box::new(domain), Box::new(codomain))
}
fn constant(name: &str) -> FTerm {
    Variable(name.to_string())
}
fn apply(fun: FTerm, args: Vec<FTerm>) -> FTerm {
    args.into_iter()
        .fold(fun, |fun, arg| Application(Box::new(fun), Box::new(arg)))
}
fn instantiate(name: &str, type_arg: FType) -> FTerm {
    TypeApplication(Box::new(constant(name)), type_arg)
}

/// Returns the System F environment of THF problems, with the base types
/// `$i`, `$o` and the logical constants
pub fn hol_environment() -> Environment<SystemF> {
    let o = boolean;
    let alpha = || Atomic("A".to_string());
    let polymorphic =
        |body: FType| Forall("A".to_string(), Box::new(kind()), Box::new(body));

    let mut environment = SystemF::default_environment();
    for base_type in [INDIVIDUAL_TYPE, BOOLEAN_TYPE] {
        environment.add_to_context(base_type, &kind());
    }
    for truth in [TRUE, FALSE] {
        environment.add_to_context(truth, &o());
    }
    environment.add_to_context(NOT, &arrow(o(), o()));
    for connective in [AND, OR, IMPLY, IFF] {
        environment.add_to_context(connective, &arrow(o(), arrow(o(), o())));
    }
    environment.add_to_context(
        EQUALS,
        &polymorphic(arrow(alpha(), arrow(alpha(), o()))),
    );
    for quantifier in [PI, SIGMA] {
        environment.add_to_context(
            quantifier,
            &polymorphic(arrow(arrow(alpha(), o()), o())),
        );
    }
    environment
}

//############################# TYPES

fn atomic_type(input: &str) -> PResult<'_, FType> {
    alt((
        map(upper_word, |name| Atomic(name.to_string())),
        map(atomic_word, Atomic),
        map(dollar_word, |name| {
            if name == TPTP_KIND {
                kind()
            } else {
                Atomic(name.to_string())
            }
        }),
    ))(input)
}

/// `[A: $tType, B]`, the type variables bound by `!>`
fn type_variables(input: &str) -> PResult<'_, Vec<String>> {
    let (input, vars) = delimited(
        sym("["),
        separated_list1(
            sym(","),
            pair(upper_word, opt(preceded(sym(":"), thf_type))),
        ),
        sym("]"),
    )(input)?;

    let mut names = vec![];
    for (var, var_kind) in vars {
        match var_kind {
            Some(var_kind) if var_kind != kind() => {
                return Err(nom::Err::Failure(LofError::unsupported(format!(
                    "Type variable {} of kind {:?} needs type operators (System Fω)",
                    var, var_kind
                ))))
            }
            _ => names.push(var.to_string()),
        }
    }
    Ok((input, names))
}

/// `!>[A: $tType]: type`
fn polymorphic_type(input: &str) -> PResult<'_, FType> {
    let (input, vars) = preceded(sym("!>"), type_variables)(input)?;
    let (input, body) = preceded(sym(":"), thf_type)(input)?;
    let polymorphic = vars.into_iter().rev().fold(body, |body, var| {
        Forall(var, Box::new(kind()), Box::new(body))
    });
    Ok((input, polymorphic))
}

fn unit_type(input: &str) -> PResult<'_, FType> {
    alt((
        polymorphic_type,
        delimited(sym("("), thf_type, sym(")")),
        atomic_type,
    ))(input)
}

/// A THF type: `$i`, `nat`, `A`, `$i > $o` (right associative),
/// `!>[A: $tType]: (A > A)`. `$tType` becomes the System F kind `*`
pub fn thf_type(input: &str) -> PResult<'_, FType> {
    let (input, domain) = unit_type(input)?;
    let (input, codomain) = opt(preceded(sym(">"), thf_type))(input)?;
    match codomain {
        Some(codomain) => Ok((input, arrow(domain, codomain))),
        None => Ok((input, domain)),
    }
}

/// Returns `true` iff the kind `*` occurs in `typee` somewhere else than as
/// the kind of a quantified type variable
fn uses_kind_as_type(typee: &FType) -> bool {
    match typee {
        Atomic(name) => name == TYPE_KIND,
        MetaVariable(_) => false,
        Arrow(domain, codomain) => {
            uses_kind_as_type(domain) || uses_kind_as_type(codomain)
        }
        Forall(_, _, body) => uses_kind_as_type(body),
    }
}

fn declaration_body(input: &str) -> PResult<'_, (String, FType)> {
    let (input, name) =
        alt((atomic_word, map(dollar_word, str::to_string)))(input)?;
    let (input, typee) = preceded(sym(":"), thf_type)(input)?;
    if typee != kind() && uses_kind_as_type(&typee) {
        return Err(nom::Err::Failure(LofError::unsupported(format!(
            "Type constructor {} of type {:?} needs type operators (System Fω)",
            name, typee
        ))));
    }
    Ok((input, (name, typee)))
}

/// Parses the formula of a `thf(name, type, ...)` annotated formula: a
/// symbol with its type, or a base type declared of type `$tType`
pub fn thf_type_declaration(input: &str) -> PResult<'_, (String, FType)> {
    alt((
        delimited(sym("("), declaration_body, sym(")")),
        declaration_body,
    ))(input)
}

//############################# TYPES
//
//
//############################# FORMULAS

fn combine(op: BinaryConnective, left: FTerm, right: FTerm) -> FTerm {
    let not = |φ: FTerm| apply(constant(NOT), vec![φ]);
    let binary =
        |name: &str, l: FTerm, r: FTerm| apply(constant(name), vec![l, r]);
    match op {
        BinaryConnective::Iff => binary(IFF, left, right),
        BinaryConnective::NotIff => not(binary(IFF, left, right)),
        BinaryConnective::Implies => binary(IMPLY, left, right),
        BinaryConnective::ImpliedBy => binary(IMPLY, right, left),
        BinaryConnective::Nor => not(binary(OR, left, right)),
        BinaryConnective::Nand => not(binary(AND, left, right)),
    }
}

fn equality(left: FTerm, right: FTerm, is_positive: bool) -> FTerm {
    let equality = apply(instantiate(EQUALS, hole()), vec![left, right]);
    if is_positive {
        equality
    } else {
        apply(constant(NOT), vec![equality])
    }
}

/// An argument of `@`, TH1 allows applying terms to types
enum ApplyArgument {
    Term(FTerm),
    Type(FType),
}

/// A parenthesized mapping or polymorphic type. Atomic type arguments are
/// indistinguishable from constants and are resolved by `elaborate`
fn compound_type_argument(input: &str) -> PResult<'_, FType> {
    let (rest, typee) = delimited(sym("("), thf_type, sym(")"))(input)?;
    match typee {
        Arrow(_, _) | Forall(_, _, _) => Ok((rest, typee)),
        _ => Err(nom::Err::Error(LofError::custom(
            "Not a compound type argument",
        ))),
    }
}

fn apply_argument(input: &str) -> PResult<'_, ApplyArgument> {
    alt((
        map(compound_type_argument, ApplyArgument::Type),
        map(unit, ApplyArgument::Term),
    ))(input)
}

/// `<thf_logic_formula>`: a unit formula, optionally followed by a non
/// associative binary connective or by a chain of `|`, `&` or `@`
fn logic_formula(input: &str) -> PResult<'_, FTerm> {
    let (input, first) = unit(input)?;

    if let Ok((input, op)) = binary_connective(input) {
        let (input, second) = unit(input)?;
        return Ok((input, combine(op, first, second)));
    }

    let (input, disjuncts) = many0(preceded(sym("|"), unit))(input)?;
    let (input, conjuncts) = if disjuncts.is_empty() {
        many0(preceded(sym("&"), unit))(input)?
    } else {
        (input, vec![])
    };
    let (input, arguments) = if disjuncts.is_empty() && conjuncts.is_empty() {
        many0(preceded(sym("@"), apply_argument))(input)?
    } else {
        (input, vec![])
    };

    // TPTP connectives don't have relative precedence, mixing requires parentheses
    if alt((sym("|"), sym("&"), sym("@"), map(binary_connective, |_| "")))(
        input,
    )
    .is_ok()
    {
        return Err(nom::Err::Failure(LofError::custom(
            "TPTP requires parentheses when mixing binary connectives",
        )));
    }

    let chain = |name: &str, operands: Vec<FTerm>| {
        operands.into_iter().fold(first.clone(), |acc, operand| {
            apply(constant(name), vec![acc, operand])
        })
    };
    let formula = if !disjuncts.is_empty() {
        chain(OR, disjuncts)
    } else if !conjuncts.is_empty() {
        chain(AND, conjuncts)
    } else {
        arguments
            .into_iter()
            .fold(first, |fun, argument| match argument {
                ApplyArgument::Term(arg) => {
                    Application(Box::new(fun), Box::new(arg))
                }
                ApplyArgument::Type(type_arg) => {
                    TypeApplication(Box::new(fun), type_arg)
                }
            })
    };
    Ok((input, formula))
}

#[derive(Clone, Copy)]
enum Binder {
    ForAll,
    Exists,
    Lambda,
    TypeForAll,
}

/// `![X: T]: φ`, `?[X: T]: φ`, `^[X: T]: t` and the TH1 `!>[A: $tType]: φ`,
/// where the body is a unit formula. Untyped term variables are `$i`
fn quantified(input: &str) -> PResult<'_, FTerm> {
    if alt((sym("?*"), sym("@+"), sym("@-")))(input).is_ok() {
        return Err(nom::Err::Failure(LofError::unsupported(
            "THF choice, description and type existential binders are not supported",
        )));
    }

    let (input, binder) = alt((
        map(sym("!>"), |_| Binder::TypeForAll),
        // don't confuse binders with `!=`, `!!` and `??`
        map(terminated(sym("!"), not(one_of("=!"))), |_| Binder::ForAll),
        map(terminated(sym("?"), not(char('?'))), |_| Binder::Exists),
        map(sym("^"), |_| Binder::Lambda),
    ))(input)?;

    if let Binder::TypeForAll = binder {
        let (input, vars) = type_variables(input)?;
        let (input, body) = preceded(sym(":"), unit)(input)?;
        let formula = vars.into_iter().rev().fold(body, |body, var| {
            TypeAbstraction(var, Box::new(kind()), Box::new(body))
        });
        return Ok((input, formula));
    }

    let (input, vars) = delimited(
        sym("["),
        separated_list1(
            sym(","),
            pair(upper_word, opt(preceded(sym(":"), thf_type))),
        ),
        sym("]"),
    )(input)?;
    let (input, body) = preceded(sym(":"), unit)(input)?;

    let mut typed_vars = vec![];
    for (var, var_type) in vars {
        let var_type =
            var_type.unwrap_or_else(|| Atomic(INDIVIDUAL_TYPE.to_string()));
        if var_type == kind() {
            return Err(nom::Err::Failure(LofError::custom(format!(
                "Type variable {} must be bound by `!>`",
                var
            ))));
        }
        typed_vars.push((var.to_string(), var_type));
    }

    let formula =
        typed_vars
            .into_iter()
            .rev()
            .fold(body, |body, (var, var_type)| {
                let lambda = Abstraction(var, var_type.clone(), Box::new(body));
                match binder {
                    Binder::ForAll => {
                        apply(instantiate(PI, var_type), vec![lambda])
                    }
                    Binder::Exists => {
                        apply(instantiate(SIGMA, var_type), vec![lambda])
                    }
                    _ => lambda,
                }
            });
    Ok((input, formula))
}

/// Connectives used as terms, eg `(&)` or `(=)`
fn connective_term(input: &str) -> PResult<'_, FTerm> {
    delimited(
        sym("("),
        alt((
            map(sym("<=>"), |_| constant(IFF)),
            map(sym("=>"), |_| constant(IMPLY)),
            map(sym("~"), |_| constant(NOT)),
            map(sym("&"), |_| constant(AND)),
            map(sym("|"), |_| constant(OR)),
            map(sym("="), |_| instantiate(EQUALS, hole())),
            map(sym("!!"), |_| instantiate(PI, hole())),
            map(sym("??"), |_| instantiate(SIGMA, hole())),
        )),
        sym(")"),
    )(input)
}

fn unitary(input: &str) -> PResult<'_, FTerm> {
    alt((
        connective_term,
        delimited(sym("("), logic_formula, sym(")")),
        map(sym("!!"), |_| instantiate(PI, hole())),
        map(sym("??"), |_| instantiate(SIGMA, hole())),
        map(upper_word, |var| constant(var)),
        map(atomic_word, |name| constant(&name)),
        map(dollar_word, |name| constant(name)),
        map(number, |literal| constant(literal)),
        map(distinct_object, |name| constant(&name)),
    ))(input)
}

/// A unitary formula, optionally compared with `=` or `!=` to another one
fn infix_or_unitary(input: &str) -> PResult<'_, FTerm> {
    let (input, left) = unitary(input)?;
    let (input, comparison) = opt(pair(
        alt((
            map(sym("!="), |_| false),
            // don't confuse `=` with the `=>` connective
            map(terminated(sym("="), not(char('>'))), |_| true),
        )),
        unitary,
    ))(input)?;

    match comparison {
        Some((is_positive, right)) => {
            Ok((input, equality(left, right, is_positive)))
        }
        None => Ok((input, left)),
    }
}

/// `<thf_unit_formula>`: quantified, negated, or a (compared) unitary formula
fn unit(input: &str) -> PResult<'_, FTerm> {
    alt((
        quantified,
        map(preceded(sym("~"), unit), |φ| apply(constant(NOT), vec![φ])),
        infix_or_unitary,
    ))(input)
}

/// Parses the formula of a non `type` `thf(...)` annotated formula into a
/// System F term. Implicit type arguments of `=`, `!!` and `??` are left
/// as holes, to be filled by `elaborate`
pub fn thf_formula(input: &str) -> PResult<'_, FTerm> {
    logic_formula(input)
}

//############################# FORMULAS
//
//
//############################# ELABORATION

/// Returns `true` iff `name` denotes a type in `environment`
fn is_type_name(environment: &Environment<SystemF>, name: &str) -> bool {
    environment
        .get_variable_type(name)
        .is_some_and(|typee| typee == kind())
}

/// Completes a parsed THF term against the `environment`, without any
/// unification:
/// * applications `f @ nat` to a name denoting a type become type
///   applications `f [nat]`
/// * the implicit type argument of `=`, `!!` and `??` is computed from the
///   type of the first term they're applied to
pub fn elaborate(
    term: &FTerm,
    environment: &mut Environment<SystemF>,
) -> Result<FTerm, LofError> {
    match term {
        Variable(_) => Ok(term.to_owned()),
        Application(fun, arg) => {
            // holes are filled below, once the type of `arg` is known
            let fun = match &**fun {
                TypeApplication(_, type_arg) if is_hole(type_arg) => {
                    (**fun).to_owned()
                }
                _ => elaborate(fun, environment)?,
            };
            if let Variable(name) = &**arg {
                if is_type_name(environment, name) {
                    return Ok(TypeApplication(
                        Box::new(fun),
                        Atomic(name.to_string()),
                    ));
                }
            }
            let arg = elaborate(arg, environment)?;

            let fun = match &fun {
                TypeApplication(constant_term, type_arg) if is_hole(type_arg) => {
                    let Variable(name) = &**constant_term else {
                        unreachable!("only constants are parsed with holes")
                    };
                    let arg_type = SystemF::type_check_term(&arg, environment)?;
                    let type_arg = if name == EQUALS {
                        arg_type
                    } else {
                        match arg_type {
                            Arrow(domain, _) => *domain,
                            other => {
                                return Err(LofError::type_mismatch(
                                    format!("`{}` argument", name),
                                    &arrow(Atomic("_".to_string()), boolean()),
                                    &other,
                                ))
                            }
                        }
                    };
                    TypeApplication(constant_term.to_owned(), type_arg)
                }
                _ => fun,
            };
            Ok(Application(Box::new(fun), Box::new(arg)))
        }
        Abstraction(var_name, var_type, body) => {
            let body = environment
                .with_local_assumption(var_name, var_type, |local_env| {
                    elaborate(body, local_env)
                })?;
            Ok(Abstraction(
                var_name.to_string(),
                var_type.to_owned(),
                Box::new(body),
            ))
        }
        TypeAbstraction(var_name, var_kind, body) => {
            let body = environment
                .with_local_assumption(var_name, var_kind, |local_env| {
                    elaborate(body, local_env)
                })?;
            Ok(TypeAbstraction(
                var_name.to_string(),
                var_kind.to_owned(),
                Box::new(body),
            ))
        }
        TypeApplication(fun, type_arg) if is_hole(type_arg) => {
            Err(LofError::custom(format!(
                "Cannot determine the type argument of {:?}, apply it to a term",
                fun
            )))
        }
        TypeApplication(fun, type_arg) => Ok(TypeApplication(
            Box::new(elaborate(fun, environment)?),
            type_arg.to_owned(),
        )),
    }
}

/// Returns `true` iff `typee` is `$o`, possibly under type quantifiers
/// (TH1 polymorphic formulas)
pub fn is_formula_type(typee: &FType) -> bool {
    match typee {
        Atomic(name) => name == BOOLEAN_TYPE,
        Forall(_, _, body) => is_formula_type(body),
        _ => false,
    }
}

//############################# ELABORATION
