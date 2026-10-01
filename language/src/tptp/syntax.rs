use crate::{error::LofError, parser::api::PResult};
use nom::{
    branch::alt,
    bytes::complete::{escaped_transform, tag, take_until, take_while},
    character::complete::{
        char, digit1, multispace1, none_of, not_line_ending, one_of, satisfy,
    },
    combinator::{map, recognize},
    error::ErrorKind,
    multi::many0,
    sequence::{delimited, pair, preceded, tuple},
};

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

/// `<lower_word> ::= <lower_alpha><alpha_numeric>*`
pub fn lower_word(input: &str) -> PResult<'_, &str> {
    preceded(
        ws0,
        recognize(pair(
            satisfy(|c| c.is_ascii_lowercase()),
            take_while(|c: char| c.is_ascii_alphanumeric() || c == '_'),
        )),
    )(input)
}

/// `<single_quoted>`: returns the content without quotes, resolving the `\'`
/// and `\\` escapes
pub fn single_quoted(input: &str) -> PResult<'_, String> {
    preceded(
        ws0,
        delimited(
            char('\''),
            escaped_transform(none_of("\\'"), '\\', one_of("\\'")),
            char('\''),
        ),
    )(input)
}

/// `<atomic_word> ::= <lower_word> | <single_quoted>`
pub fn atomic_word(input: &str) -> PResult<'_, String> {
    alt((map(lower_word, str::to_string), single_quoted))(input)
}

/// `<name> ::= <atomic_word> | <integer>`
pub fn name(input: &str) -> PResult<'_, String> {
    alt((atomic_word, map(preceded(ws0, digit1), str::to_string)))(input)
}

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
        other => Role::Other(other.to_string()),
    })(input)
}

/// Skips the optional `source` and `useful_info` annotations of an annotated
/// formula, stopping right before the closing `)` of the annotated formula.
/// Annotations may embed arbitrary formulas (eg `inference(..., [$fof(...)])`),
/// so rather than parsing them they're skipped by balancing brackets
pub fn skip_annotations(input: &str) -> PResult<'_, ()> {
    let mut depth = 0;
    for (idx, c) in input.char_indices() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' if depth == 0 => return Ok((&input[idx..], ())),
            ')' | ']' => depth -= 1,
            _ => {}
        }
    }
    Err(nom::Err::Error(LofError::parse_error(
        input,
        ErrorKind::Eof,
    )))
}
