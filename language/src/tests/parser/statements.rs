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
                Auto, Axiom, Comment, EmptyRoot, Fun, Global, HClause,
                Inductive, Solve, Theorem,
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

        let _ =
            parser.parse_notation("sugar \"_0 + _1\" := \"comb(_0, _1)\"");
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
            "sugar \"_0     *   _1\"    :=   \n\r\t \"comb(_0, _1)\"",
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
        // registering the second notation ("*") must not clobber the first
        // one ("+"): both need to be retrievable at the same time
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
            "Registering a second notation must not overwrite/lose an earlier one"
        );
        assert_eq!(
            parser.custom_notations.borrow().len(),
            2,
            "Both notations should be registered simultaneously"
        );
    }

    #[test]
    fn test_comments() {
        let parser = LofParser::new(Config::default());
        assert!(
            parser.parse_statement("#abc\n").is_ok(),
            "Parser cant read comments"
        );
        assert!(
            parser.parse_statement("#abc").is_ok(),
            "Parser cant read comments at end of input"
        );
        assert_eq!(
            parser.parse_statement("#abc").unwrap(),
            ("", Comment()),
            "Comment node isnt properly constructed"
        );
    }

    #[test]
    fn test_global() {
        let parser = LofParser::new(Config::default());
        assert!(
            parser.parse_statement("global n: nat := x;").is_ok(),
            "Parser cant read global definitions"
        );
        assert!(
            parser
                .parse_statement("global \t n  \t:  \t nat  :=\t  x  \t;")
                .is_ok(),
            "Global parser cant cope with multispaces"
        );
        assert!(
            parser.parse_statement("globaln :nat:= x;").is_err(),
            "Global parser doesnt split 'global' keyword and variable identifier"
        );
        assert_eq!(
            parser.parse_statement("global n : nat := x;").unwrap(),
            (
                "",
                Global(
                    "n".to_string(),
                    Some(VarUse("nat".to_string())),
                    VarUse("x".to_string())
                )
            ),
            "Global definition struct isnt properly constructed"
        );
        assert!(
            parser.parse_statement("global n := zero;").is_ok(),
            "Global parser doesnt support untyped definition"
        );
    }

    #[test]
    fn test_function() {
        let parser = LofParser::new(Config::default());
        assert_eq!(
            parser.parse_statement("fun f (n: Nat): Nat { s(n) }"),
            Ok((
                "",
                Fun(
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
            parser.parse_statement("fun rec f (n: Nat): Nat { f(n) }"),
            Ok((
                "",
                Fun(
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
            parser.parse_statement("fun f : TYPE { TYPE }"),
            Ok((
                "",
                Fun(
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
            parser.parse_statement("fun f (l: List(Nat)): List(Nat) { l }"),
            Ok((
                "",
                Fun(
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
            parser.parse_statement("fun f(n:Nat):Nat{n}").is_ok(),
            "Function parser cant cope with dense notation"
        );
        assert_eq!(
            parser.parse_statement(
                "fun f (n: Nat, m: Nat): Nat { plus(n, m) }"
            ),
            Ok((
                "",
                Fun(
                    "f".to_string(),
                    vec![
                        ("n".to_string(), VarUse("Nat".to_string())),
                        ("m".to_string(), VarUse("Nat".to_string()))
                    ],
                    Box::new(VarUse("Nat".to_string())),
                    Box::new(Application(
                        Box::new(VarUse("plus".to_string())),
                        vec![
                            VarUse("n".to_string()),
                            VarUse("m".to_string())
                        ]
                    )),
                    false
                )
            )),
            "Function parser doesnt support comma-separated parameter lists"
        );
        assert!(
            parser.parse_statement(
                "fun  \t \r f \r  \t  ( \t\r x \r\t :  \tNat  )  :  Nat  {  x  }"
            )
            .is_ok(),
            "Function parser cant cope with whitespaces"
        );
        assert!(
            parser
                .parse_statement("fun f (x:Unit) : Unit { let y := O; y }")
                .is_ok(),
            "Function parser doesnt support let definition in the branch"
        );

        assert!(
            parser.parse_statement("rec f : TYPE { TYPE }").is_err(),
            "Function parser accepts function with no 'fun' keyword"
        );
        assert!(
            parser
                .parse_statement("fun rec (x: TYPE): TYPE { TYPE }")
                .is_err(),
            "Function parser accepts function with no name"
        );
        assert!(
            parser
                .parse_statement("fun rec myFunction (x: TYPE) { TYPE}")
                .is_err(),
            "Function parser accepts function with no return type"
        );
        assert!(
            parser
                .parse_statement("fun rec myFunction(x: Int): Int")
                .is_err(),
            "Function parser accepts function with no body"
        );
    }

    #[test]
    fn test_axiom() {
        let parser = LofParser::new(Config::default());
        assert!(
            parser.parse_statement("axiom nat:TYPE;").is_ok(),
            "Parser cant read axioms"
        );
        assert!(
            parser.parse_statement("axiom  nat :\tTYPE  ;").is_ok(),
            "Axiom parser cant cope with multispaces"
        );
        assert!(
            parser.parse_statement("axiomnat:TYPE;").is_err(),
            "Axiom parser doesnt split 'axiom' keyword and axiom identifier"
        );
        assert_eq!(
            parser.parse_statement("axiom nat : TYPE;").unwrap(),
            (
                "",
                Axiom("nat".to_string(), Box::new(VarUse("TYPE".to_string())))
            ),
            "Axiom node isnt properly constructed"
        );
    }

    #[test]
    fn test_theorem_terms() {
        let parser = LofParser::new(Config::default());
        assert_eq!(
            parser.parse_statement("theorem p : PROP := (p)").unwrap(),
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
                .parse_statement(
                    "theorem   \tp\t  : \t PROP :=\n\t  (  \n p  \n\r)  \n\t"
                )
                .is_ok(),
            "Theorem parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_statement("lemma p : PROP := (p)").is_ok(),
            "Theorem parser doesnt support 'lemma' keyword"
        );
        assert!(
            parser
                .parse_statement("proposition p : PROP := (p)")
                .is_ok(),
            "Theorem parser doesnt support 'proposition' keyword"
        );
        assert!(
            parser.parse_statement("theoremp : PROP := (p)").is_err(),
            "Theorem parser doesnt split the keywords"
        );
        assert!(
            parser.parse_statement("theorem p:PROP:=(p)").is_ok(),
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
                .parse_statement(
                    "inductive nat : TYPE { \n| o: nat \n| \ts : nat -> nat}"
                )
                .unwrap(),
            ("", test_definition.clone()),
            "Parser cant read inductive definitions"
        );
        assert!(
            parser.parse_statement("inductive Empty : TYPE {} ").is_ok(),
            "Inductive parser doesnt support the Empty type"
        );
        assert_eq!(
            parser
                .parse_statement("inductive nat:TYPE{|o:nat|s:nat->nat}")
                .unwrap(),
            ("", test_definition.clone()),
            "Inductive parser cant cope with dense notation"
        );
        assert!(
            parser.parse_statement("inductivenat:TYPE{|o: nat|s : nat-> nat}").is_err(),
            "Inductive parser doesnt expect a whitespace after the inductive keyword"
        );
        assert_eq!(
            parser.parse_statement(
                "inductive T : TYPE { | c: list(nat) -> T | g: nat -> nat -> T}"
            )
            .unwrap(),
            (
                "",
                Inductive(
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
                "inductive list (T: TYPE) : TYPE { |nil: list(T) |cons: T -> list(T) }"
            )
            .is_ok(),
            "Inductive parser doesnt support polymorphic types"
        );
        assert!(
            parser.parse_statement(
                "inductive le : nat -> nat -> PROP { |lez: PROP | leS : PROP}"
            )
            .is_ok(),
            "Inductive parser doesnt support complex arieties"
        );
        assert!(
            parser.parse_statement(
                "inductive eq (T:TYPE, x:T) : T -> PROP { |refl: eq(T, x, x)}"
            )
            .is_ok(),
            "Inductive parser doesnt support Leibniz equality definition"
        );
    }

    #[test]
    fn test_import() {
        let parser = LofParser::new(Config::default());
        assert!(
            parser
                .parse_statement("import \"../library/logic\"")
                .is_ok(),
            "Import parser isnt working"
        );
    }

    #[test]
    fn test_import_is_deduplicated() {
        // Regression test: importing the same module more than once (be it
        // a direct repeat, or a diamond - two different imports that
        // themselves both import a shared common module) used to re-parse
        // and re-splice its entire contents again on every single import,
        // duplicating every definition once per import path leading to it.
        // That duplication compounds with every further shared import, and
        // was observed to make evaluating even a simple recursive function
        // call over the resulting environment hang. A second import of an
        // already-imported module must be a no-op instead.
        let parser = LofParser::new(Config::default());

        let (_, first) = parser
            .parse_statement("import \"../library/logic\"")
            .expect("first import must parse and actually splice the module");
        assert_ne!(
            first,
            Comment(),
            "the first import of a module must actually splice its contents"
        );

        assert_eq!(
            parser.parse_statement("import \"../library/logic\""),
            Ok(("", Comment())),
            "importing an already-imported module again must be a no-op, not re-splice it"
        );
    }

    #[test]
    fn test_theory_block() {
        let cic_parser = LofParser::new(Config::new(TypeSystem::Cic));
        let fol_parser = LofParser::new(Config::new(TypeSystem::Fol));
        assert_eq!(
            cic_parser.parse_statement("!theory_block cic TYPE !end_block"),
            Ok(("", EmptyRoot(vec![Exp(VarUse("TYPE".to_string()))]))),
            "Theory block parser didnt read the right theory block"
        );
        assert_eq!(
            fol_parser.parse_statement("!theory_block cic TYPE !end_block"),
            Ok(("", EmptyRoot(vec![]))),
            "Theory block parser didnt skip the wrong theory block"
        );
        assert!(
            fol_parser
                .parse_statement(
                    "!theory_block nonExistandSystem TYPE !end_block"
                )
                .is_err(),
            "Theory block parser parses block on non existant system id"
        );
    }

    #[test]
    fn test_auto() {
        let parser = LofParser::new(Config::new(TypeSystem::Cic));

        assert_eq!(
            parser.parse_statement("auto \\forall x:T. P(x);"),
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
            parser.parse_statement("auto\\forall x:T. P(x);").is_err(),
            "Auto parser doesnt split keyword from formula"
        );
        assert!(
            parser.parse_statement("auto \t\n\r   \\forall   x\t :\r\r T.\n\r P  \t (  x  )  \r;\n\t\t").is_ok(),
            "Auto parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_statement("auto ;").is_err(),
            "Auto parser accepts command with no formula to prove"
        );
    }

    #[test]
    fn test_auto_is_reserved_as_a_top_level_statement_keyword() {
        // Regression test: `auto` was missing from `RESERVED_KEYWORDS`
        // (unlike its sibling top-level statement keywords `solve` and
        // `hclause`, which are both reserved). Top-level source is parsed
        // node-by-node via `parse_node`, which tries `parse_expression`
        // *before* `parse_statement` - so without being reserved, `auto`
        // parsed as a bare variable reference (a seemingly harmless,
        // unbound expression statement) instead of being recognized as the
        // start of an `auto formula;` statement, silently breaking the
        // parse: the formula parsed as its own, separate expression
        // statement right after, leaving the trailing `;` as unparseable
        // leftover input. Calling `parse_statement` directly (as
        // `test_auto` above does) doesn't exercise this at all, since it
        // skips straight past `parse_node`'s ordering.
        let parser = LofParser::new(Config::new(TypeSystem::Cic));

        let (remainder, nodes) = nom::multi::many0(|input| {
            parser.parse_node(input)
        })("auto P(x);")
        .expect("a real auto statement must parse as a full document");

        assert!(
            remainder.trim().is_empty(),
            "auto statement must be fully consumed, not leave `{}` unparsed",
            remainder
        );
        assert_eq!(
            nodes.len(),
            1,
            "auto formula; must parse as a single statement node, not split into a bare `auto` expression plus a separate formula expression"
        );
    }

    #[test]
    fn test_solve() {
        let parser = LofParser::new(Config::new(TypeSystem::Cic));

        assert_eq!(
            parser.parse_statement("solve P(x)"),
            Ok((
                "",
                Solve(vec![Application(
                    Box::new(VarUse("P".to_string())),
                    vec![VarUse("x".to_string())]
                )])
            )),
            "Variable solving parser isnt producing the proper value"
        );
        assert_eq!(
            parser.parse_statement("solve P(x), Q(y)"),
            Ok((
                "",
                Solve(vec![Application(
                    Box::new(VarUse("P".to_string())),
                    vec![VarUse("x".to_string())]
                ),Application(
                    Box::new(VarUse("Q".to_string())),
                    vec![VarUse("y".to_string())]
                )])
            )),
            "Variable solving parser isnt producing the proper value with multiple goals"
        );
        assert!(
            parser.parse_statement("solvePx").is_err(),
            "Variable solving parser is accepting expression with no whitespaces"
        );
        assert!(
            parser
                .parse_statement(
                    "solve   \t\r  P  \t\r ( x )    \t\t ,  \t\n\r  Q  \t ( \n y  )   "
                )
                .is_ok(),
            "Variable solving parser cant cope with whitespaces"
        );
    }

    #[test]
    fn test_horn_clause() {
        let parser = LofParser::new(Config::new(TypeSystem::Cic));

        assert_eq!(
            parser.parse_statement("hclause P <- Q;"),
            Ok((
                "",
                HClause(VarUse("P".to_string()), vec![VarUse("Q".to_string())])
            )),
            "Horn clause parser is prducing proper value"
        );
        assert_eq!(
            parser.parse_statement("hclause P <- Q, R, S;"),
            Ok((
                "",
                HClause(VarUse("P".to_string()), vec![VarUse("Q".to_string()), VarUse("R".to_string()), VarUse("S".to_string())])
            )),
            "Horn clause parser is prducing proper value with multiple subgoals"
        );
        assert_eq!(
            parser.parse_statement("hclause A;"),
            Ok(("", HClause(VarUse("A".to_string()), vec![]))),
            "Horn clause parser is prducing proper value with empty subgoals"
        );
        assert!(
            parser.parse_statement("hclause  \r\t P \r\r\t   <-\n\t\r  Q   , \n  \t\t\r   R  ,\n   S\t\n;").is_ok(),
            "Horn clause parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_statement("hclause P<-Q,R,S;").is_ok(),
            "Horn clause parser cant cope with dense notation"
        );
        assert!(
            parser
                .parse_statement("hclause P(x, y) <- Q(x), R(y);")
                .is_ok(),
            "Horn clause parser cant cope with generalized predicates"
        );
    }
}
