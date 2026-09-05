use super::api::PResult;
use super::api::{
    Expression::{
        self, Abstraction, Application, Arrow, Inferator, Let, Match, Pipe,
        Tuple, TypeProduct, VarUse,
    },
    LofParser,
};
use super::commons::{ws0, ws1};
use crate::error::LofError;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::char,
    combinator::{map, opt},
    error::{Error, ErrorKind},
    multi::{many0, many1, separated_list1},
    sequence::{delimited, preceded, tuple},
};
use std::collections::HashMap;

//########################### EXPRESSION PARSERS
impl LofParser {
    pub fn parse_parens<'a>(&self, input: &'a str) -> PResult<'a, Expression> {
        delimited(
            preceded(ws0, char('(')),
            |input| self.parse_expression(input),
            preceded(ws0, char(')')),
        )(input)
    }
    //
    //
    fn parse_var<'a>(&self, input: &'a str) -> PResult<'a, Expression> {
        map(
            |input| self.parse_identifier(input),
            |s: &str| VarUse(s.to_string()),
        )(input)
    }
    //
    //
    fn parse_abs<'a>(&self, input: &'a str) -> PResult<'a, Expression> {
        let (input, _) =
            preceded(ws0, alt((tag("λ"), tag("\\lambda "))))(input)?;

        let (input, opt_param) = opt(preceded(
            ws0,
            //TODO: use optionally type identifier for abstractions at some point
            tuple((
                |input| self.parse_identifier(input),
                preceded(ws0, char(':')),
                preceded(ws0, |input| self.parse_type_expression(input)),
            )),
        ))(input)?;
        let (var_name, type_var) = if let Some((name, _, typ)) = opt_param {
            (name.to_string(), typ)
        } else {
            ("it".to_string(), VarUse("Unit".to_string()))
        };

        let (input, _) = preceded(ws0, char('.'))(input)?;
        let (input, body) =
            preceded(ws0, |input| self.parse_expression(input))(input)?;

        Ok((
            input,
            Abstraction(
                var_name.to_string(),
                Box::new(type_var),
                Box::new(body),
            ),
        ))
    }
    //
    //
    fn parse_type_abs<'a>(&self, input: &'a str) -> PResult<'a, Expression> {
        let (input, _) = preceded(
            ws0,
            alt((tag("Π"), tag("∀"), tag("\\forall"))),
        )(input)?;
        let (input, var_name) =
            preceded(ws0, |input| self.parse_identifier(input))(input)?;
        let (input, _) = preceded(ws0, tag(":"))(input)?;
        //TODO should allow product type expressions here or only predefined type vars?
        let (input, type_var) =
            preceded(ws0, |input| self.parse_type_expression(input))(input)?;
        let (input, _) = preceded(ws0, char('.'))(input)?;
        let (input, body) =
            preceded(ws0, |input| self.parse_expression(input))(input)?;

        Ok((
            input,
            TypeProduct(
                var_name.to_string(),
                Box::new(type_var),
                Box::new(body),
            ),
        ))
    }
    //
    //
    fn parse_arrow_type<'a>(&self, input: &'a str) -> PResult<'a, Expression> {
        let (input, domain) = alt((
            |input| self.parse_parens(input),
            |input| self.parse_app(input),
            |input| self.parse_var(input),
        ))(input)?;
        let (input, _) = preceded(ws0, tag("->"))(input)?;
        let (input, codomain) = self.parse_type_expression(input)?;

        Ok((input, Arrow(Box::new(domain), Box::new(codomain))))
    }
    //
    //
    fn applicable_expression<'a>(
        &self,
        input: &'a str,
    ) -> PResult<'a, Expression> {
        alt((
            |input| self.parse_var(input),
            |input| self.parse_abs(input),
            |input| self.parse_type_abs(input),
            // |input| self.parse_app(input),
            |input| self.parse_parens(input),
        ))(input)
    }
    fn argument_expression<'a>(
        &self,
        input: &'a str,
    ) -> PResult<'a, Expression> {
        alt((
            // custom notations must be tried before parse_app
            // otherwise if a left operand looks like a complete application
            // parse_app would greedily match just the left operand
            // leaving the rest of the notation unparsed
            |input| self.parse_custom(input),
            // application should show up before parse_var, otherwise a
            // function name followed by '(' would be parsed as a bare
            // variable and leave the rest of the argument unparsed
            |input| self.parse_app(input),
            |input| self.parse_var(input),
            |input| self.parse_meta(input),
            |input| self.parse_parens(input),
        ))(input)
    }
    fn parse_app<'a>(&self, input: &'a str) -> PResult<'a, Expression> {
        let (input, left) =
            preceded(ws0, |input| self.applicable_expression(input))(input)?;
        let (input, args) = delimited(
            preceded(ws0, char('(')),
            separated_list1(preceded(ws0, char(',')), |input| {
                self.argument_expression(input)
            }),
            preceded(ws0, preceded(opt(char(',')), preceded(ws0, char(')')))),
        )(input)?;

        Ok((input, Application(Box::new(left), args)))
    }
    //
    //
    fn parse_pattern<'a>(&self, input: &'a str) -> PResult<'a, Expression> {
        let (input, construction) = alt((
            // custom notations must be tried before parse_app
            // otherwise if a left operand looks like a complete application
            // parse_app would greedily match just the left operand
            // leaving the rest of the notation unparsed
            |input| self.parse_custom(input),
            |input| self.parse_app(input),
            |input| self.parse_var(input),
        ))(input)?;

        Ok((input, construction))
    }
    //
    //
    fn parse_match_branch<'a>(
        &self,
        input: &'a str,
    ) -> PResult<'a, (Expression, Expression)> {
        let (input, _) = preceded(ws0, char('|'))(input)?;
        let (input, pattern) = self.parse_pattern(input)?;
        let (input, _) = preceded(ws0, tag("=>"))(input)?;
        let (input, body) =
            preceded(ws0, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(ws0, char(','))(input)?;

        Ok((input, (pattern, body)))
    }
    fn parse_pattern_match<'a>(
        &self,
        input: &'a str,
    ) -> PResult<'a, Expression> {
        let (input, _) = preceded(ws0, tag("match"))(input)?;
        let (input, term) =
            preceded(ws1, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(ws1, tag("with"))(input)?;
        let (input, branches) =
            many1(|input| self.parse_match_branch(input))(input)?;

        Ok((input, Match(Box::new(term), branches)))
    }

    fn parse_meta<'a>(&self, input: &'a str) -> PResult<'a, Expression> {
        let (input, _) = preceded(ws0, char('?'))(input)?;

        Ok((input, Inferator()))
    }

    fn let_def<'a>(&self, input: &'a str) -> PResult<'a, Expression> {
        let (input, _) = preceded(ws0, tag("let"))(input)?;
        let (input, (var_name, opt_type)) = preceded(ws1, |input| {
            self.parse_optionally_typed_identifier(input)
        })(input)?;
        let (input, _) = preceded(ws0, tag(":="))(input)?;
        let (input, term) =
            preceded(ws0, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(ws0, char(';'))(input)?;
        let (input, scope) =
            preceded(ws1, |input| self.local_expression(input))(input)?;

        Ok((
            input,
            Let(
                var_name.to_string(),
                Box::new(opt_type),
                Box::new(term),
                Box::new(scope),
            ),
        ))
    }

    fn parse_pipe<'a>(&self, input: &'a str) -> PResult<'a, Expression> {
        // TODO should i avoid returning here if there's no '|' ?
        // so this doesnt conflict with other parsers
        let (input, first_type) =
            preceded(ws0, |input| self.parse_type_expression(input))(input)?;

        // parse zero or more additional types separated by '|'
        let (input, other_types) = many1(preceded(
            ws1,
            preceded(
                tag("|"),
                preceded(ws0, |input| self.parse_type_expression(input)),
            ),
        ))(input)?;

        let mut all_types = vec![first_type];
        all_types.extend(other_types);
        Ok((input, Pipe(all_types)))
    }

    fn parse_tuple<'a>(&self, input: &'a str) -> PResult<'a, Expression> {
        let (input, _) = preceded(ws0, char('('))(input)?;

        let (input, first_expr) = self.parse_expression(input)?;
        let (input, remaining_exprs) = many0(preceded(
            ws0,
            preceded(
                char(','),
                preceded(ws0, |input| self.parse_expression(input)),
            ),
        ))(input)?;

        // optional trailing comma
        let (input, _) = preceded(ws0, opt(char(',')))(input)?;
        let (input, _) = preceded(ws0, char(')'))(input)?;

        let mut all_exprs = vec![first_expr];
        all_exprs.extend(remaining_exprs);
        Ok((input, Tuple(all_exprs)))
    }

    pub fn parse_custom<'a>(&self, input: &'a str) -> PResult<'a, Expression> {
        for (_, notation) in self.custom_notations.borrow().iter() {
            let mut remaining = input;
            let mut arguments: HashMap<&str, Expression> = HashMap::new();
            let mut matched = true;

            for token in &notation.pattern_tokens {
                remaining = if token.starts_with("_") {
                    let token_parsing = self.non_custom_expression(remaining);
                    if token_parsing.is_err() {
                        matched = false;
                        break;
                    }
                    let (remaining, exp) = token_parsing?;
                    arguments.insert(token, exp);

                    remaining
                } else {
                    let token_parsing =
                        preceded(ws0, tag(token.as_str()))(remaining);
                    if token_parsing.is_err() {
                        matched = false;
                        break;
                    }
                    let (remaining, _) = token_parsing?;

                    remaining
                };
            }

            if matched {
                let mut expanded_body = (&notation.body).to_owned();
                for (name, arg) in arguments {
                    expanded_body = self.substitute(&expanded_body, name, &arg);
                }
                return Ok((remaining, expanded_body));
            }
        }

        // TODO return a better error here
        let error =
            nom::Err::Error(LofError::parse_error(input, ErrorKind::Tag));
        return Err(error);
    }

    fn non_custom_expression<'a>(
        &self,
        input: &'a str,
    ) -> PResult<'a, Expression> {
        alt((
            |input| self.parse_meta(input),
            |input| self.parse_abs(input),
            |input| self.parse_type_abs(input),
            |input| self.parse_arrow_type(input),
            // application should show up before parse_var
            // otherwise the function will be parsed as normal variable
            // and the rest of the string is not properly parsed
            |input| self.parse_app(input),
            |input| self.parse_pipe(input),
            |input| self.parse_var(input),
            |input| self.parse_parens(input),
            // parens must be tried before tuples to avoid conflicts
            |input| self.parse_tuple(input),
            |input| self.parse_pattern_match(input),
        ))(input)
    }

    pub fn local_expression<'a>(
        &self,
        input: &'a str,
    ) -> PResult<'a, Expression> {
        alt((
            |input| self.let_def(input),
            |input| self.parse_expression(input),
        ))(input)
    }

    pub fn parse_type_expression<'a>(
        &self,
        input: &'a str,
    ) -> PResult<'a, Expression> {
        alt((
            |input| self.parse_arrow_type(input),
            |input| self.parse_parens(input),
            // application should show up before parse_var
            // otherwise the function will be parsed as normal variable
            // and the rest of the string is not properly parsed
            |input| self.parse_app(input),
            |input| self.parse_var(input),
            |input| self.parse_type_abs(input),
        ))(input)
    }

    pub fn parse_expression<'a>(
        &self,
        input: &'a str,
    ) -> PResult<'a, Expression> {
        alt((
            |input| self.parse_meta(input),
            |input| self.parse_abs(input),
            |input| self.parse_type_abs(input),
            |input| self.parse_arrow_type(input),
            |input| self.let_def(input),
            |input| self.parse_pattern_match(input),
            // custom notations must be tried before parse_app
            // otherwise if a left operand looks like a complete application
            // parse_app would greedily match just the left operand
            // leaving the rest of the notation unparsed
            |input| self.parse_custom(input),
            // parse_app must come before parens for some reason
            |input| self.parse_app(input),
            |input| self.parse_parens(input),
            // parens must be tried before tuples to avoid conflicts
            |input| self.parse_tuple(input),
            |input| self.parse_pipe(input),
            // parse_var is the last one because it matches any identifiere, even
            // when it starts composite expressions. examples:
            // - parse_app starts with the name of the functions
            // - parse_pipe starts with the name of the first type
            // - parse_custom when the custom notation is infix/prefix
            |input| self.parse_var(input),
        ))(input)
    }
}
//########################### EXPRESSION PARSERS

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        config::Config,
        parser::api::{Expression::VarUse, LofParser},
    };

    #[test]
    fn test_pattern_branch() {
        let parser = LofParser::new(Config::default());

        assert!(
            parser.parse_match_branch("| O => x,").is_ok(),
            "Parser cant read pattern matching branches"
        );
        assert_eq!(
            parser.parse_match_branch("| O => x,").unwrap(),
            ("", (VarUse("O".to_string()), VarUse("x".to_string()))),
            "Pattern match branch isnt properly constructed"
        );
        assert!(
            parser.parse_match_branch("| BinTree(l, r) => x ,").is_ok(),
            "Parser cant read pattern matching branches with variables"
        );
        assert!(
            parser.parse_match_branch("| cons(?, h, l) => l,").is_ok(),
            "Parser cant read pattern matching branches with inferator"
        );
        assert!(
            parser.parse_match_branch("| O => let x := O; x,").is_ok(),
            "Match branch parser doesnt support let definition in the branch"
        );
    }

    #[test]
    fn test_pattern_on_custom() {
        let parser = LofParser::new(Config::default());
        let _ =
            parser.parse_notation("sugar \"_h :: _l\" := \"cons(?, _h, _l)\"");

        assert!(
            parser.parse_match_branch("| h :: l => l,").is_ok(),
            "Parser cant read pattern matching branches with custom notation"
        );
    }

    #[test]
    fn test_avoid_singleton_unions() {
        let parser = LofParser::new(Config::default());

        assert!(
            parser.parse_pipe(" Variable ").is_err(),
            "Pipe parser shouldnt accept single variable use as type unions"
        );
    }
}
