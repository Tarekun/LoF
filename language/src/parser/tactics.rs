use nom::branch::alt;
use nom::character::complete::multispace1;
use nom::multi::many0;
use nom::{
    bytes::complete::tag, character::complete::multispace0, sequence::preceded,
};

use super::api::Tactic::{Apply, Begin, Exact, Induction, Intro, Qed};
use super::api::{Expression, LofParser, PResult, Tactic};

//########################### TACTICS PARSER
impl LofParser {
    fn begin<'a>(
        &self,
        input: &'a str,
    ) -> PResult<'a, Tactic<Expression>> {
        let (input, _) = preceded(multispace0, tag("begin"))(input)?;
        Ok((input, Begin()))
    }

    fn qed<'a>(&self, input: &'a str) -> PResult<'a, Tactic<Expression>> {
        let (input, _) = preceded(multispace0, tag("qed."))(input)?;
        Ok((input, Qed()))
    }

    fn intro<'a>(
        &self,
        input: &'a str,
    ) -> PResult<'a, Tactic<Expression>> {
        let (input, _) = preceded(multispace0, tag("intro"))(input)?;
        let (input, (var_name, opt_type)) = preceded(multispace1, |input| {
            self.parse_optionally_typed_identifier(input)
        })(input)?;

        Ok((
            input,
            Intro(
                var_name.to_string(),
                opt_type.unwrap_or(Expression::Inferator()),
            ),
        ))
    }

    fn exact<'a>(
        &self,
        input: &'a str,
    ) -> PResult<'a, Tactic<Expression>> {
        let (input, _) = preceded(multispace0, tag("exact"))(input)?;
        let (input, proof_term) =
            preceded(multispace1, |input| self.parse_expression(input))(input)?;

        Ok((input, Exact(proof_term)))
    }

    fn apply<'a>(
        &self,
        input: &'a str,
    ) -> PResult<'a, Tactic<Expression>> {
        let (input, _) = preceded(multispace0, tag("apply"))(input)?;
        let (input, proof_term) =
            preceded(multispace1, |input| self.parse_expression(input))(input)?;

        Ok((input, Apply(proof_term)))
    }

    fn induction<'a>(
        &self,
        input: &'a str,
    ) -> PResult<'a, Tactic<Expression>> {
        let (input, _) = preceded(multispace0, tag("induction"))(input)?;
        let (input, var_name) =
            preceded(multispace1, |input| self.parse_identifier(input))(input)?;

        Ok((input, Induction(var_name.to_string())))
    }

    pub fn parse_tactic<'a>(
        &self,
        input: &'a str,
    ) -> PResult<'a, Tactic<Expression>> {
        alt((
            |input| self.begin(input),
            |input| self.qed(input),
            |input| self.intro(input),
            |input| self.apply(input),
            |input| self.exact(input),
            |input| self.induction(input),
        ))(input)
    }

    pub fn parse_interactive_proof<'a>(
        &self,
        input: &'a str,
    ) -> PResult<'a, Vec<Tactic<Expression>>> {
        let (input, _) = self.begin(input)?;
        let (input, parsed_tactics) =
            many0(|input| self.parse_tactic(input))(input)?;

        // strip begin/qed markers as they are syntactic delimiters, not proof steps
        // TODO reevaluate this approahc
        let tactics: Vec<Tactic<Expression>> = parsed_tactics
            .into_iter()
            .filter(|t| t != &Begin() && t != &Qed())
            .collect();

        Ok((input, tactics))
    }
}
//########################### TACTICS PARSER
