use super::api::Statement::{
    Auto, Axiom, Comment, EmptyRoot, Fun, Global, HClause, Inductive, Solve,
    Theorem,
};
use super::api::{Expression, LofAst, LofParser, Statement};
use super::commons::{ws0, ws1};
use crate::config::id_to_system;
use crate::misc::Union;
use crate::parser::api::Notation;
use nom::multi::separated_list1;
use nom::{
    branch::alt,
    bytes::complete::{is_not, tag},
    character::complete::{char, line_ending, multispace0, not_line_ending},
    combinator::{map, opt},
    error::{Error, ErrorKind},
    multi::many0,
    sequence::{delimited, preceded},
    IResult,
};

//########################### STATEMENT PARSERS
impl LofParser {
    fn parse_import<'a>(&self, input: &'a str) -> IResult<&'a str, Statement> {
        let (input, _) = preceded(ws0, tag("import"))(input)?;
        let (input, filepath) = preceded(
            ws0,
            delimited(char('"'), is_not("\""), char('"')),
        )(input)?;

        let (_, ast) = self.parse_source_file(&format!("{}.lof", filepath));
        match ast {
            LofAst::Stm(file_root_stm) => Ok((input, file_root_stm)),
            LofAst::Exp(_exp) => panic!("fuck this type system fr"),
        }
    }
    //
    //
    fn global<'a>(&self, input: &'a str) -> IResult<&'a str, Statement> {
        let (input, _) = preceded(ws0, tag("global"))(input)?;
        let (input, (var_name, opt_type)) = preceded(ws1, |input| {
            self.parse_optionally_typed_identifier(input)
        })(input)?;
        let (input, _) = preceded(ws0, tag(":="))(input)?;
        let (input, term) =
            preceded(ws0, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(ws0, char(';'))(input)?;

        Ok((input, Global(var_name.to_string(), opt_type, term)))
    }
    //
    //
    fn parse_function<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Statement> {
        let (input, _) = preceded(ws0, tag("fun"))(input)?;
        let (input, is_rec) = opt(preceded(ws1, tag("rec")))(input)?;
        let is_rec = is_rec.is_some();

        let (input, fun_name) =
            preceded(ws1, |input| self.parse_identifier(input))(input)?;
        let (input, args) = self.typed_parameter_list(input)?;
        let (input, _) = preceded(ws0, tag(":"))(input)?;
        let (input, output_type) =
            preceded(ws0, |input| self.parse_type_expression(input))(input)?;

        let (input, _) = preceded(ws0, tag("{"))(input)?;
        let (input, body) =
            preceded(ws0, |input| self.local_expression(input))(input)?;
        let (input, _) = preceded(ws0, tag("}"))(input)?;

        Ok((
            input,
            Fun(
                fun_name.to_string(),
                args,
                Box::new(output_type),
                Box::new(body),
                is_rec,
            ),
        ))
    }
    //
    //
    fn parse_theorem<'a>(&self, input: &'a str) -> IResult<&'a str, Statement> {
        let (input, _) = preceded(
            ws0,
            alt((tag("theorem"), tag("lemma"), tag("proposition"))),
        )(input)?;
        let (input, theorem_name) =
            preceded(ws1, |input| self.parse_identifier(input))(input)?;
        let (input, _) = preceded(ws0, tag(":"))(input)?;
        let (input, formula) =
            preceded(ws0, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(ws0, tag(":="))(input)?;

        let (input, proof) = preceded(
            ws0,
            alt((
                // term proof should be enclosed in parethesis
                map(|input| self.parse_parens(input), Union::L),
                // interactive proof
                map(|input| self.parse_interactive_proof(input), Union::R),
            )),
        )(input)?;

        Ok((input, Theorem(theorem_name.to_string(), formula, proof)))
    }
    //
    //
    fn parse_comment<'a>(&self, input: &'a str) -> IResult<&'a str, Statement> {
        // only here we need to use multispace0 or we have an infinite recursion
        let (input, _) = multispace0(input)?;
        let (input, _) = tag("#")(input)?;
        let (input, _) = not_line_ending(input)?;
        let (input, _) = opt(line_ending)(input)?;

        Ok((input, Comment()))
    }
    //
    //
    fn parse_axiom<'a>(&self, input: &'a str) -> IResult<&'a str, Statement> {
        let (input, _) = preceded(ws0, tag("axiom"))(input)?;
        let (input, axiom_name) =
            preceded(ws1, |input| self.parse_identifier(input))(input)?;
        let (input, _) = preceded(ws0, tag(":"))(input)?;
        let (input, formula) =
            preceded(ws0, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(ws0, char(';'))(input)?;

        Ok((input, Axiom(axiom_name.to_string(), Box::new(formula))))
    }
    //
    //
    fn parse_inductive_constructor<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, (String, Expression)> {
        let (input, _) = preceded(ws0, char('|'))(input)?;
        let (input, constructor_name) =
            preceded(ws0, |input| self.parse_identifier(input))(input)?;
        let (input, _) = preceded(ws0, tag(":"))(input)?;
        let (input, constructor_type) = self.parse_type_expression(input)?;

        Ok((input, (constructor_name.to_string(), constructor_type)))
    }
    fn parse_inductive_def<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Statement> {
        let (input, _) = preceded(ws0, tag("inductive"))(input)?;
        let (input, inductive_type_name) =
            preceded(ws1, |input| self.parse_identifier(input))(input)?;
        let (input, parameters) = self.typed_parameter_list(input)?;
        let (input, _) = preceded(ws0, tag(":"))(input)?;
        let (input, ariety) =
            preceded(ws0, |input| self.parse_type_expression(input))(input)?;
        let (input, _) = preceded(ws0, tag("{"))(input)?;
        let (input, constructors) =
            many0(|input| self.parse_inductive_constructor(input))(input)?;
        let (input, _) = preceded(ws0, char('}'))(input)?;

        Ok((
            input,
            Inductive(
                inductive_type_name.to_string(),
                parameters,
                Box::new(ariety),
                constructors,
            ),
        ))
    }
    //
    //
    fn prolog_query<'a>(&self, input: &'a str) -> IResult<&'a str, Statement> {
        let (input, _) = preceded(ws0, tag("solve"))(input)?;
        let (input, goals) = preceded(
            ws1,
            separated_list1(preceded(ws0, tag(",")), |i| {
                self.parse_type_expression(i)
            }),
        )(input)?;

        return Ok((input, Solve(goals)));
    }
    //
    //
    pub fn parse_theory_block<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Statement> {
        let (input, _) = preceded(ws0, tag("!theory_block"))(input)?;
        let (input, system_id) =
            preceded(ws1, |input| self.parse_identifier(input))(input)?;
        let (input, nodes) = many0(|input| self.parse_node(input))(input)?;
        let (input, _) = preceded(ws0, tag("!end_block"))(input)?;

        match id_to_system(system_id) {
            Ok(type_system) => {
                if type_system == self.config.system {
                    return Ok((input, EmptyRoot(nodes)));
                } else {
                    return Ok((input, EmptyRoot(vec![])));
                }
            }
            // TODO return a better error here
            Err(_message) => {
                let error = nom::Err::Error(Error::new(input, ErrorKind::Tag));
                return Err(error);
            }
        }
    }
    //
    //
    fn auto<'a>(&self, input: &'a str) -> IResult<&'a str, Statement> {
        let (input, _) = preceded(ws0, tag("auto"))(input)?;
        let (input, formula) =
            preceded(ws1, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(ws0, tag(";"))(input)?;

        Ok((input, Auto(formula)))
    }
    //
    //
    fn horn_clause<'a>(&self, input: &'a str) -> IResult<&'a str, Statement> {
        let (input, _) = preceded(ws0, tag("hclause"))(input)?;
        let (input, head) =
            preceded(ws0, |i| self.parse_type_expression(i))(input)?;
        let (input, subgoals) = opt(preceded(
            preceded(ws0, tag("<-")),
            preceded(
                ws0,
                separated_list1(preceded(ws0, tag(",")), |i| {
                    self.parse_type_expression(i)
                }),
            ),
        ))(input)?;
        let (input, _) = preceded(ws0, tag(";"))(input)?;

        let subgoals = subgoals.unwrap_or_else(Vec::new);
        Ok((input, HClause(head, subgoals)))
    }
    //
    //
    pub fn parse_notation<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Statement> {
        let parse_quoted =
            |input| delimited(char('"'), is_not("\""), char('"'))(input);

        let (input, _) = preceded(ws0, tag("sugar"))(input)?;
        let (input, notation) = preceded(ws1, parse_quoted)(input)?;
        let (input, _) = preceded(ws0, tag(":="))(input)?;
        let (input, body) = preceded(ws1, parse_quoted)(input)?;

        let pattern_tokens: Vec<String> =
            notation.split_whitespace().map(|s| s.to_string()).collect();
        let (_, exp) = self.parse_expression(body)?;
        self.custom_notations.borrow_mut().insert(
            0,
            Notation {
                pattern_tokens,
                body: exp,
                // precedence: 0,
            },
        );

        Ok((input, Comment()))
    }
    //
    //
    pub fn parse_statement<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Statement> {
        alt((
            |input| self.parse_comment(input),
            |input| self.global(input),
            |input| self.parse_axiom(input),
            |input| self.parse_inductive_def(input),
            |input| self.parse_theorem(input),
            |input| self.parse_function(input),
            |input| self.parse_import(input),
            |input| self.parse_theory_block(input),
            |input| self.parse_notation(input),
            |input| self.auto(input),
            |input| self.prolog_query(input),
            |input| self.horn_clause(input),
        ))(input)
    }
}
//########################### STATEMENT PARSERS
