use super::api::Statement::{
    Auto, Axiom, Comment, Equivalence, EmptyRoot, Fun, Global, HClause,
    Inductive, Solve, Theorem, Transport,
};
use super::api::{Expression, LofAst, LofParser, PResult, Statement};
use super::commons::{ws0, ws1};
use crate::config::id_to_system;
use crate::error::LofError;
use crate::misc::Union;
use crate::parser::api::Notation;
use nom::multi::separated_list1;
use nom::{
    branch::alt,
    bytes::complete::{is_not, tag},
    character::complete::{char, line_ending, multispace0, not_line_ending},
    combinator::{map, opt},
    error::ErrorKind,
    multi::many0,
    sequence::{delimited, preceded},
};

//########################### STATEMENT PARSERS
impl LofParser {
    fn parse_import<'a>(&self, input: &'a str) -> PResult<'a, Statement> {
        let (input, _) = preceded(ws0, tag("import"))(input)?;
        let (input, filepath) = preceded(
            ws0,
            delimited(char('"'), is_not("\""), char('"')),
        )(input)?;

        let (_, ast) = self
            .parse_source_file(&format!("{}.lof", filepath))
            .map_err(nom::Err::Failure)?;
        match ast {
            LofAst::Stm(file_root_stm) => Ok((input, file_root_stm)),
            LofAst::Exp(_exp) => unreachable!("fuck this type system fr"),
        }
    }
    //
    //
    fn global<'a>(&self, input: &'a str) -> PResult<'a, Statement> {
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
    fn parse_function<'a>(&self, input: &'a str) -> PResult<'a, Statement> {
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
    fn parse_theorem<'a>(&self, input: &'a str) -> PResult<'a, Statement> {
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
    fn parse_comment<'a>(&self, input: &'a str) -> PResult<'a, Statement> {
        // only here we need to use multispace0 or we have an infinite recursion
        let (input, _) = multispace0(input)?;
        let (input, _) = tag("#")(input)?;
        let (input, _) = not_line_ending(input)?;
        let (input, _) = opt(line_ending)(input)?;

        Ok((input, Comment()))
    }
    //
    //
    fn parse_axiom<'a>(&self, input: &'a str) -> PResult<'a, Statement> {
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
    ) -> PResult<'a, (String, Expression)> {
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
    ) -> PResult<'a, Statement> {
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
    fn prolog_query<'a>(&self, input: &'a str) -> PResult<'a, Statement> {
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
    ) -> PResult<'a, Statement> {
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
                let error = nom::Err::Error(LofError::parse_error(
                    input,
                    ErrorKind::Tag,
                ));
                return Err(error);
            }
        }
    }
    //
    //
    fn auto<'a>(&self, input: &'a str) -> PResult<'a, Statement> {
        let (input, _) = preceded(ws0, tag("auto"))(input)?;
        let (input, formula) =
            preceded(ws1, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(ws0, tag(";"))(input)?;

        Ok((input, Auto(formula)))
    }
    //
    //
    fn horn_clause<'a>(&self, input: &'a str) -> PResult<'a, Statement> {
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
    pub fn parse_notation<'a>(&self, input: &'a str) -> PResult<'a, Statement> {
        let parse_quoted =
            |input| delimited(char('"'), is_not("\""), char('"'))(input);

        let (input, _) = preceded(ws0, tag("sugar"))(input)?;
        let (input, notation) = preceded(ws1, parse_quoted)(input)?;
        let (input, _) = preceded(ws0, tag(":="))(input)?;
        let (input, body) = preceded(ws1, parse_quoted)(input)?;

        let pattern_tokens: Vec<String> =
            notation.split_whitespace().map(|s| s.to_string()).collect();
        let (_, exp) = self.parse_expression(body)?;
        let next_key = self.custom_notations.borrow().len() as i32;

        self.custom_notations.borrow_mut().insert(
            next_key,
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
    /// Parses one `key := expr;` field, used by `equivalence`'s
    /// forward/backward/section/retraction/dep_elim/eta entries - the same
    /// shape as `global`'s `name := body;`, just with a fixed key instead
    /// of a user-chosen name.
    fn parse_equiv_field<'a>(
        &self,
        input: &'a str,
        key: &str,
    ) -> PResult<'a, Expression> {
        let (input, _) = preceded(ws0, tag(key))(input)?;
        let (input, _) = preceded(ws0, tag(":="))(input)?;
        let (input, expr) =
            preceded(ws0, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(ws0, char(';'))(input)?;

        Ok((input, expr))
    }
    //
    //
    /// Parses one `| name => expr` entry, used by `equivalence`'s
    /// `dep_constr`/`iota` blocks. Deliberately uses `parse_type_expression`
    /// (not the full `parse_expression`) for the value, exactly like
    /// `parse_inductive_constructor` does for constructor types: the full
    /// expression grammar tries `parse_pipe` before falling back to a bare
    /// variable, which would greedily swallow a *following* `| next_entry`
    /// as if it were a type union. A parenthesized value (eg a `\lambda`)
    /// still works, since `parse_type_expression` includes `parse_parens`,
    /// which re-enters the full expression grammar inside the parens where
    /// that ambiguity can't arise.
    fn parse_named_expr_entry<'a>(
        &self,
        input: &'a str,
    ) -> PResult<'a, (String, Expression)> {
        let (input, _) = preceded(ws0, char('|'))(input)?;
        let (input, name) =
            preceded(ws0, |input| self.parse_identifier(input))(input)?;
        let (input, _) = preceded(ws0, tag("=>"))(input)?;
        let (input, expr) = self.parse_type_expression(input)?;

        Ok((input, (name.to_string(), expr)))
    }
    fn parse_named_expr_block<'a>(
        &self,
        input: &'a str,
        block_name: &str,
    ) -> PResult<'a, Vec<(String, Expression)>> {
        let (input, _) = preceded(ws0, tag(block_name))(input)?;
        let (input, _) = preceded(ws0, tag("{"))(input)?;
        let (input, entries) =
            many0(|input| self.parse_named_expr_entry(input))(input)?;
        let (input, _) = preceded(ws0, char('}'))(input)?;

        Ok((input, entries))
    }
    //
    //
    /// Declares a type equivalence, bundling the hand-authored data a
    /// `transport` invocation needs (see `docs/language/systems/transport.md`):
    /// forward/backward functions, section/retraction proofs, a `dep_elim`
    /// induction principle over the target type, an optional `eta`
    /// (defaulting to nothing - the elaborator supplies the identity), and
    /// per-constructor `dep_constr`/`iota` tables.
    fn parse_equivalence<'a>(&self, input: &'a str) -> PResult<'a, Statement> {
        let (input, _) = preceded(ws0, tag("equivalence"))(input)?;
        let (input, name) =
            preceded(ws1, |input| self.parse_identifier(input))(input)?;
        let (input, _) = preceded(ws0, tag(":"))(input)?;
        let (input, type_a) =
            preceded(ws0, |input| self.parse_type_expression(input))(input)?;
        let (input, _) = preceded(ws0, tag("<->"))(input)?;
        let (input, type_b) =
            preceded(ws0, |input| self.parse_type_expression(input))(input)?;
        let (input, _) = preceded(ws0, tag("{"))(input)?;

        let (input, forward) = self.parse_equiv_field(input, "forward")?;
        let (input, backward) = self.parse_equiv_field(input, "backward")?;
        let (input, section) = self.parse_equiv_field(input, "section")?;
        let (input, retraction) =
            self.parse_equiv_field(input, "retraction")?;
        let (input, dep_elim) = self.parse_equiv_field(input, "dep_elim")?;
        let (input, eta) =
            opt(|input| self.parse_equiv_field(input, "eta"))(input)?;
        let (input, dep_constr) =
            self.parse_named_expr_block(input, "dep_constr")?;
        let (input, iota) = self.parse_named_expr_block(input, "iota")?;

        let (input, _) = preceded(ws0, tag("}"))(input)?;

        Ok((
            input,
            Equivalence(
                name.to_string(),
                Box::new(type_a),
                Box::new(type_b),
                Box::new(forward),
                Box::new(backward),
                Box::new(section),
                Box::new(retraction),
                Box::new(dep_elim),
                eta.map(Box::new),
                dep_constr,
                iota,
            ),
        ))
    }
    //
    //
    /// Invokes transport on an already-proved `theorem` or already-defined
    /// `fun`/`global`, producing a new one about the equivalence's target
    /// type. The target type/formula is mandatory - there is deliberately
    /// no "translate the old statement automatically" pass.
    fn parse_transport<'a>(&self, input: &'a str) -> PResult<'a, Statement> {
        let (input, _) = preceded(ws0, tag("transport"))(input)?;
        let (input, new_name) =
            preceded(ws1, |input| self.parse_identifier(input))(input)?;
        let (input, _) = preceded(ws0, tag(":"))(input)?;
        let (input, new_type) =
            preceded(ws0, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(ws0, tag("from"))(input)?;
        let (input, old_name) =
            preceded(ws1, |input| self.parse_identifier(input))(input)?;
        let (input, _) = preceded(ws0, tag("using"))(input)?;
        let (input, equiv_name) =
            preceded(ws1, |input| self.parse_identifier(input))(input)?;
        let (input, _) = preceded(ws0, char(';'))(input)?;

        Ok((
            input,
            Transport(
                new_name.to_string(),
                Box::new(new_type),
                old_name.to_string(),
                equiv_name.to_string(),
            ),
        ))
    }
    //
    //
    pub fn parse_statement<'a>(
        &self,
        input: &'a str,
    ) -> PResult<'a, Statement> {
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
            |input| self.parse_equivalence(input),
            |input| self.parse_transport(input),
        ))(input)
    }
}
//########################### STATEMENT PARSERS
