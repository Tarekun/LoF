use crate::{error::LofError, parser::api::PResult};
use nom::{
    branch::alt,
    bytes::complete::{tag, take_until, take_while},
    character::complete::{
        char, digit1, multispace1, not_line_ending, one_of, satisfy,
    },
    combinator::{map, not, opt, recognize},
    multi::{many0, separated_list1},
    sequence::{delimited, pair, preceded, terminated, tuple},
};

//############################# LEXICAL LAYER

/// Skips zero or more whitespace characters, line comments (`% ...`) and
/// block comments (`/* ... */`)
pub fn ws0(input: &str) -> PResult<'_, ()> {
    let (input, _) = many0(alt((
        map(multispace1, |_| ()),
        map(pair(char('%'), not_line_ending), |_| ()),
        map(tuple((tag("/*"), take_until("*/"), tag("*/"))), |_| ()),
    )))(input)?;
    Ok((input, ()))
}

/// Parses the exact symbol `symbol` after skipping leading whitespace/comments
pub fn sym<'a>(
    symbol: &'static str,
) -> impl FnMut(&'a str) -> PResult<'a, &'a str> {
    preceded(ws0, tag(symbol))
}

fn is_alphanumeric(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// `<lower_word> ::= <lower_alpha><alpha_numeric>*`
pub fn lower_word(input: &str) -> PResult<'_, &str> {
    preceded(
        ws0,
        recognize(pair(
            satisfy(|c| c.is_ascii_lowercase()),
            take_while(is_alphanumeric),
        )),
    )(input)
}

/// `<upper_word> ::= <upper_alpha><alpha_numeric>*`, used for variables
pub fn upper_word(input: &str) -> PResult<'_, &str> {
    preceded(
        ws0,
        recognize(pair(
            satisfy(|c| c.is_ascii_uppercase()),
            take_while(is_alphanumeric),
        )),
    )(input)
}

/// `<dollar_word>` and `<dollar_dollar_word>`, eg `$true`, `$false`, `$$sys`
pub fn dollar_word(input: &str) -> PResult<'_, &str> {
    preceded(
        ws0,
        recognize(tuple((
            char('$'),
            opt(char('$')),
            satisfy(|c| c.is_ascii_lowercase()),
            take_while(is_alphanumeric),
        ))),
    )(input)
}

/// Parses the content between `delimiter`s, resolving `\<delimiter>` and `\\`
/// escapes. Returns the unescaped content without delimiters
fn delimited_string(delimiter: char) -> impl Fn(&str) -> PResult<'_, String> {
    move |input: &str| {
        let (input, _) = preceded(ws0, char(delimiter))(input)?;
        let mut content = String::new();
        let mut chars = input.char_indices();
        while let Some((idx, c)) = chars.next() {
            if c == delimiter {
                return Ok((&input[idx + c.len_utf8()..], content));
            }
            if c == '\\' {
                match chars.next() {
                    Some((_, escaped))
                        if escaped == delimiter || escaped == '\\' =>
                    {
                        content.push(escaped)
                    }
                    _ => break,
                }
            } else {
                content.push(c);
            }
        }
        Err(nom::Err::Failure(LofError::custom(format!(
            "Unterminated or malformed {}-quoted string",
            delimiter
        ))))
    }
}

/// `<single_quoted>`: returns the unescaped content, without quotes
pub fn single_quoted(input: &str) -> PResult<'_, String> {
    delimited_string('\'')(input)
}

/// `<distinct_object>`: kept *with* its double quotes, so that it never
/// collides with a plain constant of the same spelling
pub fn distinct_object(input: &str) -> PResult<'_, String> {
    map(delimited_string('"'), |content| format!("\"{}\"", content))(input)
}

/// Integer, rational (`1/2`) and real (`1.5E-3`) numbers, kept as their literal text
pub fn number(input: &str) -> PResult<'_, &str> {
    preceded(
        ws0,
        recognize(tuple((
            opt(one_of("+-")),
            digit1,
            opt(alt((
                recognize(pair(char('/'), digit1)),
                recognize(tuple((
                    opt(pair(char('.'), digit1)),
                    opt(tuple((one_of("eE"), opt(one_of("+-")), digit1))),
                ))),
            ))),
        ))),
    )(input)
}

/// `<atomic_word> ::= <lower_word> | <single_quoted>`. A quoted word that is
/// also a valid lower word is the same symbol as its unquoted version, any
/// other quoted word keeps its quotes to stay distinct from variables
pub fn atomic_word(input: &str) -> PResult<'_, String> {
    alt((
        map(lower_word, str::to_string),
        map(single_quoted, |content| {
            let is_lower_word = content
                .chars()
                .next()
                .is_some_and(|c| c.is_ascii_lowercase())
                && content.chars().all(is_alphanumeric);
            if is_lower_word {
                content
            } else {
                format!("'{}'", content)
            }
        }),
    ))(input)
}

/// `<name> ::= <atomic_word> | <integer>`
pub fn name(input: &str) -> PResult<'_, String> {
    alt((atomic_word, map(preceded(ws0, digit1), str::to_string)))(input)
}

/// A TF0 atomic type: a user sort or a defined one like `$i`, `$o`, `$int`
pub fn atomic_type(input: &str) -> PResult<'_, String> {
    alt((atomic_word, map(dollar_word, str::to_string)))(input)
}

/// Any symbol that can be applied as a function or predicate, or appear as a constant
fn functor(input: &str) -> PResult<'_, String> {
    alt((
        atomic_word,
        map(dollar_word, str::to_string),
        map(number, str::to_string),
        distinct_object,
    ))(input)
}

//############################# LEXICAL LAYER
//
//
//############################# ANNOTATED FORMULAS

#[derive(Debug, Clone, PartialEq)]
/// The role of an annotated formula
pub enum Role {
    Axiom,
    Hypothesis,
    Definition,
    Assumption,
    Lemma,
    Theorem,
    Corollary,
    Conjecture,
    NegatedConjecture,
    Plain,
    Unknown,
    /// TFF type declaration
    Type,
    Other(String),
}

pub fn role(input: &str) -> PResult<'_, Role> {
    map(lower_word, |word| match word {
        "axiom" => Role::Axiom,
        "hypothesis" => Role::Hypothesis,
        "definition" => Role::Definition,
        "assumption" => Role::Assumption,
        "lemma" => Role::Lemma,
        "theorem" => Role::Theorem,
        "corollary" => Role::Corollary,
        "conjecture" => Role::Conjecture,
        "negated_conjecture" => Role::NegatedConjecture,
        "plain" => Role::Plain,
        "unknown" => Role::Unknown,
        "type" => Role::Type,
        other => Role::Other(other.to_string()),
    })(input)
}

/// Skips the optional `source` and `useful_info` annotations of an annotated
/// formula, stopping right before the closing `)` of the annotated formula.
/// Annotations may embed arbitrary formulas (eg `inference(..., [$fof(...)])`),
/// so rather than parsing them they're skipped by balancing brackets
pub fn skip_annotations(input: &str) -> PResult<'_, ()> {
    let mut depth = 0usize;
    let mut idx = 0;
    while let Some(c) = input[idx..].chars().next() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' if depth == 0 => return Ok((&input[idx..], ())),
            ')' | ']' => depth -= 1,
            '\'' | '"' => {
                // brackets inside quoted strings don't count
                let (rest, _) = delimited_string(c)(&input[idx..])?;
                idx = input.len() - rest.len();
                continue;
            }
            _ => {}
        }
        idx += c.len_utf8();
    }
    Err(nom::Err::Error(LofError::custom(
        "Unbalanced brackets in formula annotations",
    )))
}

//############################# ANNOTATED FORMULAS
//
//
//############################# TERMS AND ATOMS

#[derive(Debug, Clone, PartialEq)]
/// Dialect-neutral term, shared by the FOF and CNF grammars before being
/// lowered to `FolTerm` or `CnfTerm`
pub enum TptpTerm {
    /// var_name
    Var(String),
    /// fun_name, [args]
    Fun(String, Vec<TptpTerm>),
}

#[derive(Debug, Clone, PartialEq)]
/// Dialect-neutral atomic formula
pub enum TptpAtom {
    /// pred_name, [args]
    Pred(String, Vec<TptpTerm>),
    /// left, right, is_positive (`=` vs `!=`)
    Eq(TptpTerm, TptpTerm, bool),
}

fn arguments(input: &str) -> PResult<'_, Vec<TptpTerm>> {
    delimited(sym("("), separated_list1(sym(","), term), sym(")"))(input)
}

pub fn term(input: &str) -> PResult<'_, TptpTerm> {
    alt((
        map(upper_word, |var| TptpTerm::Var(var.to_string())),
        map(pair(functor, opt(arguments)), |(fun, args)| {
            TptpTerm::Fun(fun, args.unwrap_or_default())
        }),
    ))(input)
}

/// Parses `s = t`, `s != t` or a predicate application `p(args)` / `p`
pub fn atomic_formula(input: &str) -> PResult<'_, TptpAtom> {
    let (input, left) = term(input)?;
    let (input, equality) = opt(pair(
        alt((
            map(sym("!="), |_| false),
            // don't confuse `=` with the `=>` connective
            map(terminated(sym("="), not(char('>'))), |_| true),
        )),
        term,
    ))(input)?;

    match (left, equality) {
        (left, Some((is_positive, right))) => {
            Ok((input, TptpAtom::Eq(left, right, is_positive)))
        }
        (TptpTerm::Fun(pred, args), None) => {
            Ok((input, TptpAtom::Pred(pred, args)))
        }
        (TptpTerm::Var(var), None) => Err(nom::Err::Failure(LofError::custom(
            format!("Variable {} cannot be used as an atomic formula", var),
        ))),
    }
}

//############################# TERMS AND ATOMS
