use nom::branch::alt;
use nom::character::complete::multispace1;
use nom::error::{Error, ErrorKind};
use nom::multi::many0;
use nom::{
    bytes::complete::tag, character::complete::multispace0, sequence::preceded,
    IResult,
};

use super::api::Tactic::{Begin, By, Intro, Qed};
use super::api::{Expression, LofParser, Tactic};

//########################### TACTICS PARSER
impl LofParser {
    fn begin<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Tactic<Expression>> {
        let (input, _) = preceded(multispace0, tag("begin"))(input)?;
        Ok((input, Begin()))
    }

    fn qed<'a>(&self, input: &'a str) -> IResult<&'a str, Tactic<Expression>> {
        let (input, _) = preceded(multispace0, tag("qed."))(input)?;
        Ok((input, Qed()))
    }

    fn intro<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Tactic<Expression>> {
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

    fn by<'a>(&self, input: &'a str) -> IResult<&'a str, Tactic<Expression>> {
        let (input, _) = preceded(multispace0, tag("by"))(input)?;
        let (input, proof_term) =
            preceded(multispace1, |input| self.parse_expression(input))(input)?;

        Ok((input, By(proof_term)))
    }

    pub fn parse_tactic<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Tactic<Expression>> {
        alt((
            |input| self.begin(input),
            |input| self.qed(input),
            |input| self.intro(input),
            |input| self.by(input),
        ))(input)
    }

    pub fn parse_interactive_proof<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Vec<Tactic<Expression>>> {
        let (input, partial_proof) =
            many0(|input| self.parse_tactic(input))(input)?;

        if partial_proof.len() > 0 && partial_proof[0] != Begin() {
            // TODO return a better error here
            // return Err("Interactive proofs must start with a 'begin' tactic");
            let error = nom::Err::Error(Error::new(input, ErrorKind::Tag));
            return Err(error);
        }
        Ok((input, partial_proof))
    }
}
//########################### TACTICS PARSER
