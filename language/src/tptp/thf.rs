use super::syntax::{atomic_word, dollar_word, sym, upper_word};
use crate::{
    parser::api::PResult,
    type_theory::{
        cic::cic::{
            CicTerm::{
                self, Abstraction, Application, Meta, Product, Sort, Variable,
            },
            NameKind, HOLE_INDEX,
        },
        grammars::traits::LocallyNameless,
    },
};
use nom::{
    branch::alt,
    character::complete::char,
    combinator::{map, not, opt},
    multi::{many1, separated_list1},
    sequence::{delimited, pair, preceded, separated_pair, terminated},
};

#[derive(Debug, Clone, PartialEq)]
/// The content of a `thf` annotated formula
pub enum ThfInput {
    /// `symbol: type`, the declaration of a constant or of a type
    Declaration(String, CicTerm),
    /// A formula, a term of type `$o`
    Formula(CicTerm),
}

/// A global constant: a user symbol, a defined one like `$i`, `$o`, or a
/// logical constant like `&`, `!!`
fn constant(name: &str) -> CicTerm {
    Variable(name.to_string(), NameKind::Const())
}

/// The application of `fun` to every argument of `args`, in order
fn apply(fun: CicTerm, args: Vec<CicTerm>) -> CicTerm {
    args.into_iter()
        .fold(fun, |fun, arg| Application(Box::new(fun), Box::new(arg)))
}

fn not_(φ: CicTerm) -> CicTerm {
    apply(constant("~"), vec![φ])
}

/// The polymorphic `=` applied to `left` and `right`, its type argument is
/// left as a hole
fn equality(left: CicTerm, right: CicTerm) -> CicTerm {
    apply(constant("="), vec![Meta(HOLE_INDEX), left, right])
}

/// Parses the content of a `thf` annotated formula: a type declaration or a
/// formula
pub fn thf_input(input: &str) -> PResult<'_, ThfInput> {
    fn declaration(input: &str) -> PResult<'_, (String, CicTerm)> {
        alt((
            separated_pair(atomic_word, sym(":"), thf_formula),
            delimited(sym("("), declaration, sym(")")),
        ))(input)
    }
    alt((
        map(declaration, |(symbol, typee)| {
            ThfInput::Declaration(symbol, typee)
        }),
        map(thf_formula, ThfInput::Formula),
    ))(input)
}

/// `<thf_logic_formula>`, also used for types: a unit formula, optionally
/// followed by either a non associative binary connective and another unit
/// formula, or a chain of `|`, `&`, `@` or `>`. TPTP connectives have no
/// relative precedence, so anything else needs parentheses
pub fn thf_formula(input: &str) -> PResult<'_, CicTerm> {
    let (input, first) = unit(input)?;

    let connective = alt((
        sym("<=>"),
        sym("<~>"),
        sym("=>"),
        sym("<="),
        sym("~|"),
        sym("~&"),
    ));
    if let Ok((input, (op, second))) = pair(connective, unit)(input) {
        let binary = |op, l, r| apply(constant(op), vec![l, r]);
        let formula = match op {
            "<=>" => binary("<=>", first, second),
            "<~>" => not_(binary("<=>", first, second)),
            "=>" => binary("=>", first, second),
            "<=" => binary("=>", second, first),
            "~|" => not_(binary("|", first, second)),
            "~&" => not_(binary("&", first, second)),
            _ => unreachable!(),
        };
        return Ok((input, formula));
    }
    for op in ["|", "&"] {
        if let Ok((input, rest)) = many1(preceded(sym(op), unit))(input) {
            let formula = rest.into_iter().fold(first, |left, right| {
                apply(constant(op), vec![left, right])
            });
            return Ok((input, formula));
        }
    }
    if let Ok((input, args)) = many1(preceded(sym("@"), unit))(input) {
        return Ok((input, apply(first, args)));
    }
    // `A > B > C` is `A > (B > C)`
    if let Ok((input, rest)) = many1(preceded(sym(">"), unit))(input) {
        let types = [vec![first], rest].concat();
        let formula = types.into_iter().rev().reduce(|codomain, domain| {
            Product("_".to_string(), Box::new(domain), Box::new(codomain))
        });
        return Ok((input, formula.unwrap()));
    }
    Ok((input, first))
}

/// `<thf_unit_formula>`: a negation, an equation `s = t` / `s != t` or a
/// unitary formula
fn unit(input: &str) -> PResult<'_, CicTerm> {
    if let Ok((input, φ)) = preceded(sym("~"), unit)(input) {
        return Ok((input, not_(φ)));
    }
    let (input, left) = unitary(input)?;
    // don't confuse `=` with the `=>` connective
    let equals = terminated(sym("="), not(char('>')));
    let (input, equation) =
        opt(pair(alt((equals, sym("!="))), unitary))(input)?;
    let formula = match equation {
        Some(("!=", right)) => not_(equality(left, right)),
        Some((_, right)) => equality(left, right),
        None => left,
    };
    Ok((input, formula))
}

/// `<thf_unitary_formula>`: quantified, parenthesized or atomic
fn unitary(input: &str) -> PResult<'_, CicTerm> {
    alt((
        quantified,
        delimited(sym("("), thf_formula, sym(")")),
        map(upper_word, |var| {
            Variable(var.to_string(), NameKind::Local())
        }),
        map(sym("$tType"), |_| Sort("TYPE".to_string())),
        // `!!` and `??` are the quantifiers as terms, `!! @ p` is `![X]: p @ X`
        map(alt((sym("!!"), sym("??"), dollar_word)), |name| {
            if name == "!!" || name == "??" {
                apply(constant(name), vec![Meta(HOLE_INDEX)])
            } else {
                constant(name)
            }
        }),
        map(atomic_word, |name| constant(&name)),
    ))(input)
}

/// `Q [X1: τ1, ..., Xn: τn] : φ`, where `φ` is a unit formula:
/// - `!` and `?` are the polymorphic constants `!!` and `??` applied to the
///   type of the variable and to the abstraction of the body over it
/// - `^` is a λ-abstraction
/// - TH1 `!>` is a product, a quantification over types
fn quantified(input: &str) -> PResult<'_, CicTerm> {
    let (input, quantifier) =
        alt((sym("!>"), sym("!"), sym("?"), sym("^")))(input)?;
    let (input, variables) = delimited(
        sym("["),
        separated_list1(
            sym(","),
            separated_pair(upper_word, sym(":"), thf_formula),
        ),
        pair(sym("]"), sym(":")),
    )(input)?;
    let (input, body) = unit(input)?;

    let formula =
        variables
            .into_iter()
            .rev()
            .fold(body, |body, (var, typee)| {
                let abstraction = Abstraction(
                    var.to_string(),
                    Box::new(typee.clone()),
                    Box::new(body.close(var)),
                );
                match quantifier {
                    "!" => apply(constant("!!"), vec![typee, abstraction]),
                    "?" => apply(constant("??"), vec![typee, abstraction]),
                    "^" => abstraction,
                    // TODO a formula quantified over types is a product, which is
                    // only a term of type `$o` if `$o` is read as the sort of
                    // propositions rather than as an opaque type
                    _ => Product(
                        var.to_string(),
                        Box::new(typee),
                        Box::new(body.close(var)),
                    ),
                }
            });
    Ok((input, formula))
}
