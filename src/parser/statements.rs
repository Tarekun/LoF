use super::api::Statement::{Auto, Theorem};
use super::api::{Expression, LofAst, LofParser, Statement};
use crate::config::id_to_system;
use crate::misc::Union;
use crate::parser::api::Notation;
use nom::{
    branch::alt,
    bytes::complete::{is_not, tag},
    character::complete::{
        char, line_ending, multispace0, multispace1, not_line_ending,
    },
    combinator::{map, opt},
    error::{Error, ErrorKind},
    multi::many0,
    sequence::{delimited, preceded},
    IResult,
};

//########################### STATEMENT PARSERS
impl LofParser {
    fn parse_import<'a>(&self, input: &'a str) -> IResult<&'a str, Statement> {
        let (input, _) = preceded(multispace0, tag("import"))(input)?;
        let (input, filepath) = preceded(
            multispace0,
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
    pub fn global<'a>(&self, input: &'a str) -> IResult<&'a str, Statement> {
        let (input, _) = preceded(multispace0, tag("global"))(input)?;
        let (input, (var_name, opt_type)) = preceded(multispace1, |input| {
            self.parse_optionally_typed_identifier(input)
        })(input)?;
        let (input, _) = preceded(multispace0, tag(":="))(input)?;
        let (input, term) =
            preceded(multispace0, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(multispace0, char(';'))(input)?;

        Ok((
            input,
            Statement::Global(var_name.to_string(), opt_type, Box::new(term)),
        ))
    }
    //
    //
    pub fn parse_function<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Statement> {
        let (input, _) = preceded(multispace0, tag("fun"))(input)?;
        let (input, is_rec) = opt(preceded(multispace1, tag("rec")))(input)?;
        let is_rec = is_rec.is_some();

        let (input, fun_name) =
            preceded(multispace1, |input| self.parse_identifier(input))(input)?;
        let (input, args) = self.typed_parameter_list(input)?;
        let (input, _) = preceded(multispace0, tag(":"))(input)?;
        let (input, output_type) =
            preceded(multispace0, |input| self.parse_type_expression(input))(
                input,
            )?;

        let (input, _) = preceded(multispace0, tag("{"))(input)?;
        let (input, body) =
            preceded(multispace0, |input| self.local_expression(input))(input)?;
        let (input, _) = preceded(multispace0, tag("}"))(input)?;

        Ok((
            input,
            Statement::Fun(
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
    pub fn parse_theorem<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Statement> {
        let (input, _) = preceded(
            multispace0,
            alt((tag("theorem"), tag("lemma"), tag("proposition"))),
        )(input)?;
        let (input, theorem_name) =
            preceded(multispace1, |input| self.parse_identifier(input))(input)?;
        let (input, _) = preceded(multispace0, tag(":"))(input)?;
        let (input, formula) =
            preceded(multispace0, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(multispace0, tag(":="))(input)?;

        let (input, proof) = preceded(
            multispace0,
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
    pub fn parse_comment<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Statement> {
        let (input, _) = multispace0(input)?;
        let (input, _) = tag("#")(input)?;
        let (input, _) = not_line_ending(input)?;
        let (input, _) = opt(line_ending)(input)?;

        Ok((input, Statement::Comment()))
    }
    //
    //
    pub fn parse_axiom<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Statement> {
        let (input, _) = preceded(multispace0, tag("axiom"))(input)?;
        let (input, axiom_name) =
            preceded(multispace1, |input| self.parse_identifier(input))(input)?;
        let (input, _) = preceded(multispace0, tag(":"))(input)?;
        let (input, formula) =
            preceded(multispace0, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(multispace0, char(';'))(input)?;

        Ok((
            input,
            Statement::Axiom(axiom_name.to_string(), Box::new(formula)),
        ))
    }
    //
    //
    pub fn parse_inductive_constructor<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, (String, Expression)> {
        let (input, _) = preceded(multispace0, char('|'))(input)?;
        let (input, constructor_name) =
            preceded(multispace0, |input| self.parse_identifier(input))(input)?;
        let (input, _) = preceded(multispace0, tag(":"))(input)?;
        let (input, constructor_type) = self.parse_type_expression(input)?;

        Ok((input, (constructor_name.to_string(), constructor_type)))
    }
    pub fn parse_inductive_def<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Statement> {
        let (input, _) = preceded(multispace0, tag("inductive"))(input)?;
        let (input, inductive_type_name) =
            preceded(multispace1, |input| self.parse_identifier(input))(input)?;
        let (input, parameters) = self.typed_parameter_list(input)?;
        let (input, _) = preceded(multispace0, tag(":"))(input)?;
        let (input, ariety) =
            preceded(multispace0, |input| self.parse_type_expression(input))(
                input,
            )?;
        let (input, _) = preceded(multispace0, tag("{"))(input)?;
        let (input, constructors) =
            many0(|input| self.parse_inductive_constructor(input))(input)?;
        let (input, _) = preceded(multispace0, char('}'))(input)?;

        Ok((
            input,
            Statement::Inductive(
                inductive_type_name.to_string(),
                parameters,
                Box::new(ariety),
                constructors,
            ),
        ))
    }
    //
    //
    pub fn parse_theory_block<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Statement> {
        let (input, _) = preceded(multispace0, tag("!theory_block"))(input)?;
        let (input, system_id) =
            preceded(multispace1, |input| self.parse_identifier(input))(input)?;
        let (input, nodes) = many0(|input| self.parse_node(input))(input)?;
        let (input, _) = preceded(multispace0, tag("!end_block"))(input)?;

        match id_to_system(system_id) {
            Ok(type_system) => {
                if type_system == self.config.system {
                    return Ok((input, Statement::EmptyRoot(nodes)));
                } else {
                    return Ok((input, Statement::EmptyRoot(vec![])));
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
    pub fn auto<'a>(&self, input: &'a str) -> IResult<&'a str, Statement> {
        let (input, _) = preceded(multispace0, tag("auto"))(input)?;
        let (input, formula) =
            preceded(multispace1, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(multispace0, tag(";"))(input)?;

        Ok((input, Auto(formula)))
    }
    //
    //
    pub fn parse_notation<'a>(
        &self,
        input: &'a str,
    ) -> IResult<&'a str, Statement> {
        let parse_quoted =
            |input| delimited(char('"'), is_not("\""), char('"'))(input);

        let (input, _) = preceded(multispace0, tag("sugar"))(input)?;
        let (input, notation) = preceded(multispace1, parse_quoted)(input)?;
        let (input, _) = preceded(multispace0, tag(":="))(input)?;
        let (input, body) = preceded(multispace1, parse_quoted)(input)?;

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

        Ok((input, Statement::Comment()))
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
        ))(input)
    }
}
//########################### STATEMENT PARSERS

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        config::{Config, TypeSystem},
        misc::Union,
        parser::api::{
            Expression::{Application, Arrow, TypeProduct, VarUse},
            LofAst::Exp,
            LofParser, Notation,
            Statement::{
                self, Auto, Axiom, Comment, EmptyRoot, Global, Inductive,
                Theorem,
            },
        },
    };

    #[test]
    fn test_notation() {
        fn notation_contains(parser: &LofParser, notation: Notation) -> bool {
            for (_, n) in parser.custom_notations.borrow().iter() {
                if n.body == notation.body
                    && n.pattern_tokens == notation.pattern_tokens
                {
                    return true;
                }
            }

            false
        }

        let parser = LofParser::new(Config::default());

        let _ = parser.parse_notation("sugar \"_0 + _1\" := \"comb _0 _1\"");
        assert!(
            notation_contains(
                &parser,
                Notation {
                    pattern_tokens: vec![
                        "_0".to_string(),
                        "+".to_string(),
                        "_1".to_string()
                    ],
                    body: Application(
                        Box::new(VarUse("comb".to_string())),
                        vec![
                            VarUse("_0".to_string()),
                            VarUse("_1".to_string())
                        ]
                    )
                }
            ),
            "Notation parser didnt store tokens or parse the body properly"
        );

        let _ = parser.parse_notation(
            "sugar \"_0     *   _1\"    :=   \n\r\t \"comb _0 _1\"",
        );
        assert!(
            notation_contains(
                &parser,
                Notation {
                    pattern_tokens: vec![
                        "_0".to_string(),
                        "*".to_string(),
                        "_1".to_string()
                    ],
                    body: Application(
                        Box::new(VarUse("comb".to_string())),
                        vec![
                            VarUse("_0".to_string()),
                            VarUse("_1".to_string())
                        ]
                    )
                }
            ),
            "Notation parser didnt trim whitespaces"
        );
    }

    #[test]
    fn test_comments() {
        let parser = LofParser::new(Config::default());
        assert!(
            parser.parse_comment("#abc\n").is_ok(),
            "Parser cant read comments"
        );
        assert!(
            parser.parse_comment("#abc").is_ok(),
            "Parser cant read comments at end of input"
        );
        assert_eq!(
            parser.parse_comment("#abc").unwrap(),
            ("", Comment()),
            "Comment node isnt properly constructed"
        );
    }

    #[test]
    fn test_global() {
        let parser = LofParser::new(Config::default());
        assert!(
            parser.global("global n: nat := x;").is_ok(),
            "Parser cant read global definitions"
        );
        assert!(
            parser
                .global("global \t n  \t:  \t nat  :=\t  x  \t;")
                .is_ok(),
            "Global parser cant cope with multispaces"
        );
        assert!(
            parser.global("globaln :nat:= x;").is_err(),
            "Global parser doesnt split 'global' keyword and variable identifier"
        );
        assert_eq!(
            parser.global("global n : nat := x;").unwrap(),
            (
                "",
                Global(
                    "n".to_string(),
                    Some(VarUse("nat".to_string())),
                    Box::new(VarUse("x".to_string()))
                )
            ),
            "Global definition struct isnt properly constructed"
        );
        assert!(
            parser.global("global n := zero;").is_ok(),
            "Global parser doesnt support untyped definition"
        );
        assert!(
            parser.parse_statement("global n: nat := x;").is_ok(),
            "Top level parser can't read global definitions"
        );
    }

    #[test]
    fn test_function() {
        let parser = LofParser::new(Config::default());
        assert_eq!(
            parser.parse_function("fun f (n: Nat): Nat { s n }"),
            Ok((
                "",
                Statement::Fun(
                    "f".to_string(),
                    vec![("n".to_string(), VarUse("Nat".to_string()))],
                    Box::new(VarUse("Nat".to_string())),
                    Box::new(Application(
                        Box::new(VarUse("s".to_string())),
                        vec![VarUse("n".to_string())]
                    )),
                    false
                )
            )),
            "Function parser doesnt construct the statement properly"
        );
        assert_eq!(
            parser.parse_function("fun rec f (n: Nat): Nat { f n }"),
            Ok((
                "",
                Statement::Fun(
                    "f".to_string(),
                    vec![("n".to_string(), VarUse("Nat".to_string()))],
                    Box::new(VarUse("Nat".to_string())),
                    Box::new(Application(
                        Box::new(VarUse("f".to_string())),
                        vec![VarUse("n".to_string())]
                    )),
                    true
                )
            )),
            "Function parser doesnt recognize recursive functions"
        );

        assert_eq!(
            parser.parse_function("fun f : TYPE { TYPE }"),
            Ok((
                "",
                Statement::Fun(
                    "f".to_string(),
                    vec![],
                    Box::new(VarUse("TYPE".to_string())),
                    Box::new(VarUse("TYPE".to_string())),
                    false
                )
            )),
            "Function parser cant cope with functions with no arguments"
        );
        assert_eq!(
            parser.parse_function("fun f (l: List Nat): List Nat { l }"),
            Ok((
                "",
                Statement::Fun(
                    "f".to_string(),
                    vec![(
                        "l".to_string(),
                        Application(
                            Box::new(VarUse("List".to_string())),
                            vec![VarUse("Nat".to_string())]
                        )
                    )],
                    Box::new(Application(
                        Box::new(VarUse("List".to_string())),
                        vec![VarUse("Nat".to_string())]
                    )),
                    Box::new(VarUse("l".to_string())),
                    false
                )
            )),
            "Function parser cant cope with arguments that have application types"
        );
        assert!(
            parser.parse_function("fun f(n:Nat):Nat{n}").is_ok(),
            "Function parser cant cope with dense notation"
        );
        assert!(
            parser.parse_function(
                "fun  \t \r f \r  \t  ( \t\r x \r\t :  \tNat  )  :  Nat  {  x  }"
            )
            .is_ok(),
            "Function parser cant cope with whitespaces"
        );
        assert!(
            parser
                .parse_statement("fun f (l: List Nat): List Nat { l }")
                .is_ok(),
            "Top level stm parser doesnt recognize functions"
        );
        assert!(
            parser
                .parse_function("fun f (x:Unit) : Unit { let y := O; y }")
                .is_ok(),
            "Function parser doesnt support let definition in the branch"
        );

        assert!(
            parser.parse_function("rec f : TYPE { TYPE }").is_err(),
            "Function parser accepts function with no 'fun' keyword"
        );
        assert!(
            parser
                .parse_function("fun rec (x: TYPE): TYPE { TYPE }")
                .is_err(),
            "Function parser accepts function with no name"
        );
        assert!(
            parser
                .parse_function("fun rec myFunction (x: TYPE) { TYPE}")
                .is_err(),
            "Function parser accepts function with no return type"
        );
        assert!(
            parser
                .parse_function("fun rec myFunction(x: Int): Int")
                .is_err(),
            "Function parser accepts function with no body"
        );
    }

    #[test]
    fn test_axiom() {
        let parser = LofParser::new(Config::default());
        assert!(
            parser.parse_axiom("axiom nat:TYPE;").is_ok(),
            "Parser cant read axioms"
        );
        assert!(
            parser.parse_axiom("axiom  nat :\tTYPE  ;").is_ok(),
            "Axiom parser cant cope with multispaces"
        );
        assert!(
            parser.parse_axiom("axiomnat:TYPE;").is_err(),
            "Axiom parser doesnt split 'axiom' keyword and axiom identifier"
        );
        assert_eq!(
            parser.parse_axiom("axiom nat : TYPE;").unwrap(),
            (
                "",
                Axiom("nat".to_string(), Box::new(VarUse("TYPE".to_string())))
            ),
            "Axiom node isnt properly constructed"
        );
        assert!(
            parser.parse_statement("axiom nat:TYPE;").is_ok(),
            "Top level parser can't read axioms"
        );
    }

    #[test]
    fn test_theorem_terms() {
        let parser = LofParser::new(Config::default());
        assert_eq!(
            parser.parse_theorem("theorem p : PROP := (p)").unwrap(),
            (
                "",
                Theorem(
                    "p".to_string(),
                    VarUse("PROP".to_string()),
                    Union::L(VarUse("p".to_string())),
                )
            ),
            "Parser cant theorem proofs"
        );
        assert!(
            parser
                .parse_theorem(
                    "theorem   \tp\t  : \t PROP :=\n\t  (  \n p  \n\r)  \n\t"
                )
                .is_ok(),
            "Theorem parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_theorem("lemma p : PROP := (p)").is_ok(),
            "Theorem parser doesnt support 'lemma' keyword"
        );
        assert!(
            parser.parse_theorem("proposition p : PROP := (p)").is_ok(),
            "Theorem parser doesnt support 'proposition' keyword"
        );
        assert!(
            parser.parse_theorem("theoremp : PROP := (p)").is_err(),
            "Theorem parser doesnt split the keywords"
        );
        assert!(
            parser.parse_theorem("theorem p:PROP:=(p)").is_ok(),
            "Theorem parser doesnt accept dense text"
        );
    }

    #[test]
    fn test_inductive() {
        let parser = LofParser::new(Config::default());
        let test_definition = Inductive(
            "nat".to_string(),
            vec![],
            Box::new(VarUse("TYPE".to_string())),
            vec![
                ("o".to_string(), VarUse("nat".to_string())),
                (
                    "s".to_string(),
                    Arrow(
                        Box::new(VarUse("nat".to_string())),
                        Box::new(VarUse("nat".to_string())),
                    ),
                ),
            ],
        );

        assert_eq!(
            parser
                .parse_inductive_def(
                    "inductive nat : TYPE { \n| o: nat \n| \ts : nat -> nat}"
                )
                .unwrap(),
            ("", test_definition.clone()),
            "Parser cant read inductive definitions"
        );
        assert!(
            parser
                .parse_inductive_def("inductive Empty : TYPE {} ")
                .is_ok(),
            "Inductive parser doesnt support the Empty type"
        );
        assert_eq!(
            parser
                .parse_inductive_def("inductive nat:TYPE{|o:nat|s:nat->nat}")
                .unwrap(),
            ("", test_definition.clone()),
            "Inductive parser cant cope with dense notation"
        );
        assert!(
            parser.parse_inductive_def("inductivenat:TYPE{|o: nat|s : nat-> nat}").is_err(),
            "Inductive parser doesnt expect a whitespace after the inductive keyword"
        );
        assert_eq!(
            parser.parse_inductive_def(
                "inductive T : TYPE { | c: (list nat) -> T | g: nat -> nat -> T}"
            )
            .unwrap(),
            (
                "",
                Statement::Inductive(
                    "T".to_string(),
                    vec![],
                    Box::new(VarUse("TYPE".to_string())),
                    vec![
                        (
                            "c".to_string(),
                            Arrow(
                                Box::new(Application(
                                    Box::new(VarUse(
                                        "list".to_string()
                                    )),
                                    vec![VarUse("nat".to_string())],
                                )),
                                Box::new(VarUse("T".to_string()))
                            )
                        ),
                        (
                            "g".to_string(),
                            Arrow(
                                Box::new(VarUse("nat".to_string())),
                                Box::new(Arrow(
                                    Box::new(VarUse("nat".to_string())),
                                    Box::new(VarUse("T".to_string())),
                                ))
                            ),
                        ),
                    ],
                )
            ),
            "Inductive constructor parser cant properly parse constructor types"
        );
        assert!(
            parser.parse_statement(
                "inductive T: TYPE { \n\t| c:(list nat) ->T \n\t| g: nat -> nat->T}"
            )
            .is_ok(),
            "Top level parser cant parse inductive definitions"
        );

        assert!(
            parser.parse_inductive_def(
                "inductive list (T: TYPE) : TYPE { |nil: (list T) |cons: T -> (list T) }"
            )
            .is_ok(),
            "Inductive parser doesnt support polymorphic types"
        );
        assert!(
            parser.parse_inductive_def(
                "inductive le : nat -> nat -> PROP { |lez: PROP | leS : PROP}"
            )
            .is_ok(),
            "Inductive parser doesnt support complex arieties"
        );
        assert!(
            parser.parse_inductive_def(
                "inductive eq (T:TYPE) (x:T) : T -> PROP { |refl: (((eq T) x) x)}"
            )
            .is_ok(),
            "Inductive parser doesnt support Leibniz equality definition"
        );
    }

    #[test]
    fn test_import() {
        let parser = LofParser::new(Config::default());
        assert!(
            parser.parse_import("import \"library/logic\"").is_ok(),
            "Import parser isnt working"
        );
        assert!(
            parser.parse_statement("import \"library/logic\"").is_ok(),
            "Top level statement parser doesnt support import"
        );
    }

    #[test]
    fn test_theory_block() {
        let cic_parser = LofParser::new(Config::new(TypeSystem::Cic()));
        let fol_parser = LofParser::new(Config::new(TypeSystem::Fol()));
        assert_eq!(
            cic_parser.parse_theory_block("!theory_block cic TYPE !end_block"),
            Ok(("", EmptyRoot(vec![Exp(VarUse("TYPE".to_string()))]))),
            "Theory block parser didnt read the right theory block"
        );
        assert_eq!(
            fol_parser.parse_theory_block("!theory_block cic TYPE !end_block"),
            Ok(("", EmptyRoot(vec![]))),
            "Theory block parser didnt skip the wrong theory block"
        );
        assert!(
            fol_parser
                .parse_theory_block(
                    "!theory_block nonExistandSystem TYPE !end_block"
                )
                .is_err(),
            "Theory block parser parses block on non existant system id"
        );
        assert!(
            cic_parser
                .parse_statement("!theory_block cic TYPE !end_block")
                .is_ok(),
            "Top level parser doesnt support theory blocks"
        );
    }

    #[test]
    fn test_auto() {
        let parser = LofParser::new(Config::new(TypeSystem::Cic()));

        assert_eq!(
            parser.parse_statement("auto \\forall x:T. P x;"),
            Ok((
                "",
                Auto(TypeProduct(
                    "x".to_string(),
                    Box::new(VarUse("T".to_string())),
                    Box::new(Application(
                        Box::new(VarUse("P".to_string())),
                        vec![VarUse("x".to_string())]
                    ))
                ))
            )),
            "Parser cant process auto commands"
        );
        assert!(
            parser.parse_statement("auto\\forall x:T. P x;").is_err(),
            "Auto parser doesnt split keyword from formula"
        );
        assert!(
            parser.parse_statement("auto \t\n\r   \\forall   x\t :\r\r T.\n\r P    x  \r;\n\t\t").is_ok(),
            "Auto parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_statement("auto ;").is_err(),
            "Auto parser accepts command with no formula to prove"
        );
    }
}
