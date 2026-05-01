use super::api::{
    Expression::{
        self, Abstraction, Application, Arrow, Inferator, Let, Match, Pipe,
        Tuple, TypeProduct, VarUse,
    },
    LofParser,
};
use crate::misc::simple_map;
use nom::{
    bytes::complete::{tag, take_while1},
    character::complete::{char, multispace0},
    combinator::{opt, recognize},
    error::{Error, ErrorKind},
    multi::many0,
    sequence::{delimited, preceded},
    IResult,
};

const RESERVED_KEYWORDS: &[&str] = &[
    "let",
    "global",
    "axiom",
    "inductive",
    "match",
    "with",
    "theorem",
    "lemma",
    "proposition",
    "qed",
    "fun",
    "rec",
    "import",
    "begin",
    "qed.",
    "intro",
    "exact",
    "sugar",
    "query",
    "hclause",
    "solve",
];

impl LofParser {
    pub fn parse_identifier<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, &'a str> {
        let (input, identifier) = preceded(
            multispace0,
            recognize(take_while1(|c: char| {
                c == '_'
                    || unicode_xid::UnicodeXID::is_xid_start(c)
                    || unicode_xid::UnicodeXID::is_xid_continue(c)
            })),
        )(input)?;

        if RESERVED_KEYWORDS.contains(&identifier) {
            Err(nom::Err::Error(Error::new(input, ErrorKind::Tag)))
        } else {
            Ok((input, identifier))
        }
    }

    pub fn parse_typed_identifier<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, (String, Expression)> {
        let (input, identifier) =
            preceded(multispace0, |input| self.parse_identifier(input))(input)?;
        let (input, _) = preceded(multispace0, tag(":"))(input)?;
        let (input, type_expression) =
            preceded(multispace0, |input| self.parse_type_expression(input))(
                input,
            )?;

        Ok((input, (identifier.to_string(), type_expression)))
    }

    pub fn parse_optionally_typed_identifier<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, (String, Option<Expression>)> {
        let (input, identifier) =
            preceded(multispace0, |input| self.parse_identifier(input))(input)?;

        let (input, opt_type) = opt(preceded(
            multispace0,
            preceded(
                tag(":"),
                preceded(multispace0, |input| {
                    self.parse_type_expression(input)
                }),
            ),
        ))(input)?;

        Ok((input, (identifier.to_string(), opt_type)))
    }

    pub fn typed_parameter_list<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Vec<(String, Expression)>> {
        many0(preceded(
            multispace0,
            delimited(
                preceded(multispace0, char('(')),
                |input| self.parse_typed_identifier(input),
                preceded(multispace0, char(')')),
            ),
        ))(input)
    }
    pub fn substitute(
        &self,
        exp: &Expression,
        target_name: &str,
        body: &Expression,
    ) -> Expression {
        match exp {
            // base case
            VarUse(name) => {
                if name == target_name {
                    body.to_owned()
                } else {
                    exp.to_owned()
                }
            }

            // binder variants
            Abstraction(var_name, var_type, fun_body) => {
                if var_name == target_name {
                    // shadowing of target_name inside the function body
                    exp.to_owned()
                } else {
                    Abstraction(
                        var_name.to_string(),
                        var_type.to_owned(),
                        Box::new(self.substitute(fun_body, target_name, body)),
                    )
                }
            }
            TypeProduct(var_name, var_type, for_body) => {
                if var_name == target_name {
                    // shadowing of target_name inside the function body
                    exp.to_owned()
                } else {
                    TypeProduct(
                        var_name.to_string(),
                        var_type.to_owned(),
                        Box::new(self.substitute(for_body, target_name, body)),
                    )
                }
            }
            Let(var_name, var_type, definition_body, scope) => {
                let var_type = if var_type.is_some() {
                    let type_unwrapped = (**var_type).as_ref().unwrap();
                    Some(self.substitute(&type_unwrapped, target_name, body))
                } else {
                    None
                };
                let definition_body =
                    self.substitute(definition_body, target_name, body);
                let scope = if var_name == target_name {
                    (**scope).to_owned()
                } else {
                    self.substitute(scope, target_name, body)
                };

                Let(
                    var_name.to_string(),
                    Box::new(var_type),
                    Box::new(definition_body),
                    Box::new(scope),
                )
            }

            // binary variants
            Arrow(left, right) => Arrow(
                Box::new(self.substitute(left, target_name, body)),
                Box::new(self.substitute(right, target_name, body)),
            ),
            // n-ary variants
            Application(fun, args) => Application(
                Box::new(self.substitute(fun, target_name, body)),
                // TODO avoid cloning
                simple_map(args.to_owned(), |arg| {
                    self.substitute(&arg, target_name, body)
                }),
            ),
            Pipe(formulas) => {
                // TODO avoid cloning
                Pipe(simple_map(formulas.to_owned(), |formula| {
                    self.substitute(&formula, target_name, body)
                }))
            }
            Tuple(terms) => Tuple(simple_map(terms.to_owned(), |term| {
                // TODO avoid cloning
                self.substitute(&term, target_name, body)
            })),

            // this bs
            Match(matched_term, branches) => Match(
                Box::new(self.substitute(matched_term, target_name, body)),
                //TODO avoid cloning
                simple_map(branches.clone(), |(pattern, patter_body)| {
                    (
                        self.substitute(&pattern, target_name, body),
                        self.substitute(&patter_body, target_name, body),
                    )
                }),
            ),
            // non recursive
            Inferator() => exp.to_owned(),
        }
    }
}
