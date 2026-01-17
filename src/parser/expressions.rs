use super::api::{
    Expression::{
        self, Abstraction, Application, Arrow, Inferator, Let, Match, Pipe,
        Tuple, TypeProduct, VarUse,
    },
    LofParser,
};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, multispace0, multispace1},
    combinator::{map, opt},
    error::{Error, ErrorKind},
    multi::{many0, many1},
    sequence::{delimited, preceded},
    IResult,
};
use std::collections::HashMap;

//########################### EXPRESSION PARSERS
impl LofParser {
    pub fn parse_parens<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        delimited(
            preceded(multispace0, char('(')),
            |input| self.parse_expression(input),
            preceded(multispace0, char(')')),
        )(input)
    }
    //
    //
    pub fn parse_var<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        map(
            |input| self.parse_identifier(input),
            |s: &str| VarUse(s.to_string()),
        )(input)
    }
    //
    //
    pub fn parse_abs<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        let (input, _) =
            preceded(multispace0, alt((tag("λ"), tag("\\lambda "))))(input)?;
        let (input, var_name) =
            preceded(multispace0, |input| self.parse_identifier(input))(input)?;
        let (input, _) = preceded(multispace0, tag(":"))(input)?;
        //TODO should allow product type expressions here or only predefined type vars?
        let (input, type_var) =
            preceded(multispace0, |input| self.parse_type_expression(input))(
                input,
            )?;
        let (input, _) = preceded(multispace0, char('.'))(input)?;
        let (input, body) =
            preceded(multispace0, |input| self.parse_expression(input))(input)?;

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
    pub fn parse_type_abs<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        let (input, _) = preceded(
            multispace0,
            alt((tag("Π"), tag("∀"), tag("\\forall"))),
        )(input)?;
        let (input, var_name) =
            preceded(multispace0, |input| self.parse_identifier(input))(input)?;
        let (input, _) = preceded(multispace0, tag(":"))(input)?;
        //TODO should allow product type expressions here or only predefined type vars?
        let (input, type_var) =
            preceded(multispace0, |input| self.parse_type_expression(input))(
                input,
            )?;
        let (input, _) = preceded(multispace0, char('.'))(input)?;
        let (input, body) =
            preceded(multispace0, |input| self.parse_expression(input))(input)?;

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
    pub fn parse_arrow_type<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        let (input, domain) = alt((
            |input| self.parse_parens(input),
            |input| self.parse_app(input),
            |input| self.parse_var(input),
        ))(input)?;
        let (input, _) = preceded(multispace0, tag("->"))(input)?;
        let (input, codomain) = self.parse_type_expression(input)?;

        Ok((input, Arrow(Box::new(domain), Box::new(codomain))))
    }
    //
    //
    fn applicable_expression<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
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
    ) -> IResult<&'a str, Expression> {
        alt((
            |input| self.parse_var(input),
            |input| self.parse_meta(input),
            |input| self.parse_parens(input),
        ))(input)
    }
    pub fn parse_app<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        let (input, left) =
            preceded(multispace0, |input| self.applicable_expression(input))(
                input,
            )?;
        let (input, args) = many1(preceded(multispace1, |input| {
            self.argument_expression(input)
        }))(input)?;

        Ok((input, Application(Box::new(left), args)))
    }
    //
    //
    fn parse_pattern<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        let (input, construction) = alt((
            |input| self.parse_app(input),
            |input| self.parse_custom(input),
            |input| self.parse_var(input),
        ))(input)?;

        Ok((input, construction))
    }
    //
    //
    pub fn parse_match_branch<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, (Expression, Expression)> {
        let (input, _) = preceded(multispace0, char('|'))(input)?;
        let (input, pattern) = self.parse_pattern(input)?;
        let (input, _) = preceded(multispace0, tag("=>"))(input)?;
        let (input, body) =
            preceded(multispace0, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(multispace0, char(','))(input)?;

        Ok((input, (pattern, body)))
    }
    pub fn parse_pattern_match<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        let (input, _) = preceded(multispace0, tag("match"))(input)?;
        let (input, term) =
            preceded(multispace1, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(multispace1, tag("with"))(input)?;
        let (input, branches) =
            many1(|input| self.parse_match_branch(input))(input)?;

        Ok((input, Match(Box::new(term), branches)))
    }

    pub fn parse_meta<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        let (input, _) = preceded(multispace0, char('?'))(input)?;

        Ok((input, Inferator()))
    }

    fn let_def<'a>(&self, input: &'a str) -> IResult<&'a str, Expression> {
        let (input, _) = preceded(multispace0, tag("let"))(input)?;
        let (input, (var_name, opt_type)) = preceded(multispace1, |input| {
            self.parse_optionally_typed_identifier(input)
        })(input)?;
        let (input, _) = preceded(multispace0, tag(":="))(input)?;
        let (input, term) =
            preceded(multispace0, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(multispace0, char(';'))(input)?;
        let (input, scope) =
            preceded(multispace1, |input| self.local_expression(input))(input)?;

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

    pub fn parse_pipe<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        // TODO should i avoid returning here if there's no '|' ?
        // so this doesnt conflict with other parsers
        let (input, first_type) =
            preceded(multispace0, |input| self.parse_type_expression(input))(
                input,
            )?;

        // parse zero or more additional types separated by '|'
        let (input, other_types) = many1(preceded(
            multispace1,
            preceded(
                tag("|"),
                preceded(multispace0, |input| {
                    self.parse_type_expression(input)
                }),
            ),
        ))(input)?;

        let mut all_types = vec![first_type];
        all_types.extend(other_types);
        Ok((input, Pipe(all_types)))
    }

    pub fn parse_tuple<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        let (input, _) = preceded(multispace0, char('('))(input)?;

        let (input, first_expr) = self.parse_expression(input)?;
        let (input, remaining_exprs) = many0(preceded(
            multispace0,
            preceded(
                char(','),
                preceded(multispace0, |input| self.parse_expression(input)),
            ),
        ))(input)?;

        // optional trailing comma
        let (input, _) = preceded(multispace0, opt(char(',')))(input)?;
        let (input, _) = preceded(multispace0, char(')'))(input)?;

        let mut all_exprs = vec![first_expr];
        all_exprs.extend(remaining_exprs);
        Ok((input, Tuple(all_exprs)))
    }

    fn parse_custom<'a>(&self, input: &'a str) -> IResult<&'a str, Expression> {
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
                        preceded(multispace0, tag(token.as_str()))(remaining);
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
        let error = nom::Err::Error(Error::new(input, ErrorKind::Tag));
        return Err(error);
    }

    fn non_custom_expression<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
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
    ) -> IResult<&'a str, Expression> {
        alt((
            |input| self.let_def(input),
            |input| self.parse_expression(input),
        ))(input)
    }

    pub fn parse_expression<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        alt((
            |input| self.parse_meta(input),
            |input| self.parse_abs(input),
            |input| self.parse_type_abs(input),
            |input| self.parse_arrow_type(input),
            |input| self.let_def(input),
            |input| self.parse_pattern_match(input),
            // parse_app must come before parens for some reason
            |input| self.parse_app(input),
            |input| self.parse_parens(input),
            // parens must be tried before tuples to avoid conflicts
            |input| self.parse_tuple(input),
            |input| self.parse_pipe(input),
            |input| self.parse_custom(input),
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
        parser::api::{
            Expression::{
                Abstraction, Application, Arrow, Inferator, Let, Match, Pipe,
                Tuple, TypeProduct, VarUse,
            },
            LofParser,
        },
    };

    #[test]
    fn test_notation() {
        let parser = LofParser::new(Config::default());

        let _ = parser.parse_notation("sugar \"_0 + _1\" := \"add _0 _1\"");
        assert_eq!(
            parser.parse_custom("n + m"),
            Ok((
                "",
                Application(
                    Box::new(VarUse("add".to_string())),
                    vec![VarUse("n".to_string()), VarUse("m".to_string())]
                )
            )),
            "Parser couldnt pick up simple binary infix custom notation"
        );
        assert_eq!(
            parser.parse_custom("n   \t\r +   \t\t\nm"),
            Ok((
                "",
                Application(
                    Box::new(VarUse("add".to_string())),
                    vec![VarUse("n".to_string()), VarUse("m".to_string())]
                )
            )),
            "Custom notation parser cant cope with whitespaces"
        );
        assert_eq!(
            parser.parse_custom("(n + m) + o"),
            Ok((
                "",
                Application(
                    Box::new(VarUse("add".to_string())),
                    vec![
                        Application(
                            Box::new(VarUse("add".to_string())),
                            vec![
                                VarUse("n".to_string()),
                                VarUse("m".to_string()),
                            ]
                        ),
                        VarUse("o".to_string())
                    ]
                )
            )),
            "composti non funzionano"
        );
        let _ = parser.parse_notation("sugar \"_0 ++ _1\" := \"add _1 _0\"");
        assert_eq!(
            parser.parse_custom("n ++ m"),
            Ok((
                "",
                Application(
                    Box::new(VarUse("add".to_string())),
                    vec![VarUse("m".to_string()), VarUse("n".to_string())]
                )
            )),
            "Custom notation parser cant track arguments properly"
        );

        let _ = parser.parse_notation("sugar \"_h :: _l\" := \"cons ? _h _l\"");
        assert_eq!(
            parser.parse_custom("h :: l"),
            Ok((
                "",
                Application(
                    Box::new(VarUse("cons".to_string())),
                    vec![
                        Inferator(),
                        VarUse("h".to_string()),
                        VarUse("l".to_string())
                    ]
                )
            )),
            "Custom notation parser list doenst work properly"
        );
    }

    #[test]
    fn test_parens() {
        let parser = LofParser::new(Config::default());
        assert!(
            parser.parse_parens("(x)").is_ok(),
            "Parser cant cope with parenthesis"
        );
        assert!(
            parser.parse_parens("((x))").is_ok(),
            "Parser cant cope with nested parenthesis"
        );
        assert!(
            parser.parse_parens("(x").is_err(),
            "Parser accepts unmatched parenthesis"
        );
        assert!(
            parser.parse_parens("x)").is_err(),
            "Parser accepts unmatched parenthesis"
        );
        assert_eq!(
            parser.parse_parens("(x)").unwrap(),
            ("", VarUse("x".to_string())),
            "Parenthesis parser doesnt produce subterm properly"
        );
    }

    #[test]
    fn test_type_theory_terms() {
        let parser = LofParser::new(Config::default());
        // variable
        assert!(
            parser.parse_var("test").is_ok(),
            "Parser cant read variables"
        );
        assert_eq!(
            parser.parse_var("  test\n").unwrap(),
            ("\n", VarUse("test".to_string())),
            "Variable parser cant cope with whitespaces"
        );

        // abstraction
        assert!(
            parser.parse_abs("λx:T.x").is_ok(),
            "Parser cant read lambda abstractions"
        );
        assert!(
            parser.parse_abs("λ \tx   :\tT \t . \t x  \n").is_ok(),
            "Abstraction parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_abs("\\lambda   x :T .  x").is_ok(),
            "Abstraction parser cant use 'lambda' keyword"
        );
        assert_eq!(
            parser.parse_abs("λn:nat.n").unwrap(),
            (
                "",
                Abstraction(
                    "n".to_string(),
                    Box::new(VarUse("nat".to_string())),
                    Box::new(VarUse("n".to_string()))
                )
            ),
            "Abstraction struct isnt properly built"
        );

        // type abstraction
        assert!(
            parser.parse_type_abs("ΠT:TYPE.T").is_ok(),
            "Parser cant read type abstractions"
        );
        assert!(
            parser
                .parse_type_abs("Π \tT   :\tTYPE \t . \t T  \n")
                .is_ok(),
            "Type abstraction parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_type_abs("\\forall   T :TYPE .  T").is_ok(),
            "Type abstraction parser cant use 'forall' keyword"
        );
        assert_eq!(
            parser.parse_type_abs("ΠT:TYPE.T").unwrap(),
            (
                "",
                TypeProduct(
                    "T".to_string(),
                    Box::new(VarUse("TYPE".to_string())),
                    Box::new(VarUse("T".to_string()))
                )
            ),
            "Abstraction struct isnt properly built"
        );
    }

    #[test]
    fn test_application() {
        let parser = LofParser::new(Config::default());
        assert_eq!(
            parser.parse_app("f x").unwrap(),
            (
                "",
                Application(
                    Box::new(VarUse("f".to_string())),
                    vec![VarUse("x".to_string())]
                )
            ),
            "Parser cant read function application"
        );
        assert_eq!(
            parser.parse_expression("f x").unwrap(),
            (
                "",
                Application(
                    Box::new(VarUse("f".to_string())),
                    vec![VarUse("x".to_string())]
                )
            ),
            "Expression parser doesnt recognize application"
        );

        assert_eq!(
            parser.parse_app("f x y z").unwrap(),
            (
                "",
                Application(
                    Box::new(VarUse("f".to_string())),
                    vec![
                        VarUse("x".to_string()),
                        VarUse("y".to_string()),
                        VarUse("z".to_string())
                    ]
                )
            ),
            "Parser should implement left-associative application"
        );

        assert_eq!(
            parser.parse_app("f (x y) z").unwrap(),
            (
                "",
                Application(
                    Box::new(VarUse("f".to_string())),
                    vec![
                        Application(
                            Box::new(VarUse("x".to_string())),
                            vec![VarUse("y".to_string())],
                        ),
                        VarUse("z".to_string())
                    ]
                )
            ),
            "Application parser messes up associativity with parenthesis"
        );
    }

    #[test]
    fn test_arrow_expression() {
        let parser = LofParser::new(Config::default());
        assert_eq!(
            parser.parse_arrow_type("A -> B").unwrap(),
            (
                "",
                Arrow(
                    Box::new(VarUse("A".to_string())),
                    Box::new(VarUse("B".to_string()))
                )
            ),
            "Parser cant read type arrow expressions"
        );
        assert!(
            parser.parse_arrow_type(" \tA   \t \t -> \t B  \n").is_ok(),
            "Arrow expression parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_arrow_type("A->B").is_ok(),
            "Arrow expression parser cant cope with dense notation"
        );
        assert!(
            parser.parse_expression("A->B").is_ok(),
            "Top level parser cant read type arrow expressions"
        );
    }

    #[test]
    fn test_let() {
        let parser = LofParser::new(Config::default());

        assert!(
            parser.let_def("let z: Nat := zero;\nbody").is_ok(),
            "Parser cant read let definitions"
        );
        assert!(
            parser
                .let_def("let \t x  \t:  \t Nat  :=\t  x;  \t\n\r\t\t x")
                .is_ok(),
            "Let parser cant cope with multispaces"
        );
        assert!(
            parser.let_def("letn :Nat:= zero;\n n").is_err(),
            "Let parser doesnt split 'let' keyword and variable identifier"
        );
        assert!(
            parser.let_def("let n := zero;\n n").is_ok(),
            "Let parser doesnt support untyped definition"
        );
        assert_eq!(
            parser.let_def("let n : Nat := zero; n").unwrap(),
            (
                "",
                Let(
                    "n".to_string(),
                    Box::new(Some(VarUse("Nat".to_string()))),
                    Box::new(VarUse("zero".to_string())),
                    Box::new(VarUse("n".to_string()))
                )
            ),
            "Let definition struct isnt properly constructed"
        );
        assert!(
            parser.parse_node("let z: Nat := zero;\nbody").is_ok(),
            "Top level parser cant read let definitions"
        );
    }

    #[test]
    fn test_let_support() {
        let parser = LofParser::new(Config::default());

        assert!(
            parser.local_expression("let n : Nat := zero;\n  n").is_ok(),
            "Dedicated top-level parser still doesnt work with let definitions"
        );
        assert!(
            parser
                .parse_statement("fun f (x: X) : X { let y := x; x }")
                .is_ok(),
            "Function parser doesnt support let definition in the function body"
        );
    }

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
            parser.parse_match_branch("| BinTree l r => x ,").is_ok(),
            "Parser cant read pattern matching branches with variables"
        );
        assert!(
            parser.parse_match_branch("| cons ? h l => l,").is_ok(),
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
        let _ = parser.parse_notation("sugar \"_h :: _l\" := \"cons ? _h _l\"");

        assert!(
            parser.parse_match_branch("| h :: l => l,").is_ok(),
            "Parser cant read pattern matching branches with custom notation"
        );
    }

    #[test]
    fn test_pattern_matching() {
        let parser = LofParser::new(Config::default());

        assert_eq!(
            parser
                .parse_pattern_match("match x with | O => x,")
                .unwrap(),
            (
                "",
                Match(
                    Box::new(VarUse("x".to_string())),
                    vec![(VarUse("O".to_string()), VarUse("x".to_string()))]
                )
            ),
            "Pattern match expression isnt properly constructed"
        );
        assert!(
            parser
                .parse_pattern_match("match \tx   with \n\t|O =>  \nx   , \n ")
                .is_ok(),
            "Pattern match parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_pattern_match("matchx with | O => x,").is_err(),
            "Pattern match parser doesnt split keywords"
        );
        assert!(
            parser.parse_pattern_match("match xwith | O => x,").is_err(),
            "Pattern match parser doesnt split keywords"
        );
    }

    #[test]
    fn test_pipe_expression() {
        let parser = LofParser::new(Config::default());

        assert_eq!(
            parser.parse_pipe("A | B").unwrap(),
            (
                "",
                Pipe(vec![VarUse("A".to_string()), VarUse("B".to_string())])
            ),
            "Pipe expression for union type isnt working"
        );
        assert_eq!(
            parser.parse_expression("A | B").unwrap(),
            (
                "",
                Pipe(vec![VarUse("A".to_string()), VarUse("B".to_string())])
            ),
            "Top level expression parser doesnt support pipes"
        );
        assert!(
            parser.parse_pipe(" Variable ").is_err(),
            "Pipe parser shouldnt accept single variable use as type unions"
        );

        assert_eq!(
            parser.parse_pipe("A | B | C | D").unwrap(),
            (
                "",
                Pipe(vec![
                    VarUse("A".to_string()),
                    VarUse("B".to_string()),
                    VarUse("C".to_string()),
                    VarUse("D".to_string()),
                ])
            ),
            "Pipe expression doesnt support n-ary unions"
        );

        assert_eq!(
            parser.parse_pipe("A \n\t \r   |  \n \r\tB").unwrap(),
            (
                "",
                Pipe(vec![VarUse("A".to_string()), VarUse("B".to_string())])
            ),
            "Pipe expression cant cope with whitespaces"
        );
    }

    #[test]
    fn test_tuple() {
        let parser = LofParser::new(Config::default());

        assert_eq!(
            parser.parse_tuple("(one, two, three)"),
            Ok((
                "",
                Tuple(vec![
                    VarUse("one".to_string()),
                    VarUse("two".to_string()),
                    VarUse("three".to_string()),
                ])
            )),
            "Tuple parser isnt working properly"
        );
        assert!(
            parser.parse_tuple("(one, two, three,)").is_ok(),
            "Tuple parser doesnt support optional trailing comma"
        );
        assert!(
            parser
                .parse_tuple(
                    "(  \n\t one,  \n\r   two   \t , \r\r\t three   \n)"
                )
                .is_ok(),
            "Tuple parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_expression("(one, two, three)").is_ok(),
            "Top level expression parser doesnt support tuples"
        );

        assert_eq!(
            parser.parse_expression("(one)"),
            Ok(("", VarUse("one".to_string()),)),
            "Tuple parser parser likely conflicts with the parenthesis one"
        );
        assert_eq!(
            parser.parse_expression("(one,)"),
            Ok(("", Tuple(vec![VarUse("one".to_string())]))),
            "Singleton tuples cant be parsed properly"
        );
    }

    #[test]
    fn test_infer_operator() {
        let parser = LofParser::new(Config::default());

        assert!(
            parser.parse_meta("?").is_ok(),
            "parser doesnt support the infer operator ?"
        );

        assert!(
            parser.parse_meta("\n  \t\r\r\t  ?").is_ok(),
            "parser doesnt support the infer operator ? preceeded by whitespaces"
        );

        assert!(
            parser.parse_expression("  ? ").is_ok(),
            "top level parser doesnt support the infer operator ?"
        );

        assert_eq!(
            parser.parse_expression("cons ? z l"),
            Ok((
                "",
                Application(
                    Box::new(VarUse("cons".to_string())),
                    vec![
                        Inferator(),
                        VarUse("z".to_string()),
                        VarUse("l".to_string())
                    ]
                )
            )),
            "Metavariable parser doesnt integrate with applications"
        )
    }
}
