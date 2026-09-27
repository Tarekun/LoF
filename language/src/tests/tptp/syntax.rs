#[cfg(test)]
mod unit_tests {
    use crate::tptp::syntax::{
        atomic_formula, atomic_word, distinct_object, dollar_word, name,
        number, role, single_quoted, skip_annotations, term, upper_word, ws0,
        Role, TptpAtom, TptpTerm,
    };

    fn var(name: &str) -> TptpTerm {
        TptpTerm::Var(name.to_string())
    }
    fn fun(name: &str, args: Vec<TptpTerm>) -> TptpTerm {
        TptpTerm::Fun(name.to_string(), args)
    }

    #[test]
    fn test_comments() {
        assert_eq!(
            ws0("  % line comment\n  /* block\n comment */ \t rest"),
            Ok(("rest", ())),
            "Whitespace parser doesnt skip line and block comments"
        );
        assert_eq!(
            ws0("%only a comment"),
            Ok(("", ())),
            "Whitespace parser doesnt skip a comment ending the input"
        );
    }

    #[test]
    fn test_words() {
        assert_eq!(upper_word(" X1_a,"), Ok((",", "X1_a")));
        assert!(
            upper_word("x").is_err(),
            "Lowercase words are parsed as variables"
        );
        assert_eq!(dollar_word("$false)"), Ok((")", "$false")));
        assert_eq!(dollar_word("$$system"), Ok(("", "$$system")));
        assert_eq!(name("42,"), Ok((",", "42".to_string())));
    }

    #[test]
    fn test_quoted_words() {
        assert_eq!(
            single_quoted(r"'it\'s \\ ok'"),
            Ok(("", r"it's \ ok".to_string())),
            "Single quoted parser doesnt resolve escapes"
        );
        assert_eq!(
            atomic_word("'abc'"),
            Ok(("", "abc".to_string())),
            "Quoting a lower word should give the same symbol as the plain word"
        );
        assert_eq!(
            atomic_word("'Hello World'"),
            Ok(("", "'Hello World'".to_string())),
            "Quoted words that arent lower words should keep their quotes"
        );
        assert_eq!(
            distinct_object("\"distinct\""),
            Ok(("", "\"distinct\"".to_string()))
        );
        assert!(single_quoted("'unterminated").is_err());
    }

    #[test]
    fn test_numbers() {
        assert_eq!(number("12)"), Ok((")", "12")));
        assert_eq!(number("-3/4"), Ok(("", "-3/4")));
        assert_eq!(number("1.5E-3"), Ok(("", "1.5E-3")));
    }

    #[test]
    fn test_roles() {
        assert_eq!(role("axiom"), Ok(("", Role::Axiom)));
        assert_eq!(
            role("negated_conjecture"),
            Ok(("", Role::NegatedConjecture))
        );
        assert_eq!(role("type"), Ok(("", Role::Other("type".to_string()))));
    }

    #[test]
    fn test_skip_annotations() {
        assert_eq!(
            skip_annotations(
                " inference(res, [status(thm)], [$fof(p & q), 'a)b']) ). rest"
            ),
            Ok(("). rest", ())),
            "Annotation skipping doesnt stop at the closing parenthesis"
        );
        assert!(
            skip_annotations("file('a.p', [unbalanced").is_err(),
            "Annotation skipping accepts unbalanced brackets"
        );
    }

    #[test]
    fn test_terms() {
        assert_eq!(
            term("f(X, g(a), 'B c', 1, \"d\")"),
            Ok((
                "",
                fun(
                    "f",
                    vec![
                        var("X"),
                        fun("g", vec![fun("a", vec![])]),
                        fun("'B c'", vec![]),
                        fun("1", vec![]),
                        fun("\"d\"", vec![]),
                    ]
                )
            )),
            "Term parser doesnt handle nested applications and constants"
        );
    }

    #[test]
    fn test_atomic_formulas() {
        assert_eq!(
            atomic_formula("p(X)"),
            Ok(("", TptpAtom::Pred("p".to_string(), vec![var("X")])))
        );
        assert_eq!(
            atomic_formula("$true"),
            Ok(("", TptpAtom::Pred("$true".to_string(), vec![])))
        );
        assert_eq!(
            atomic_formula("f(X) = a"),
            Ok((
                "",
                TptpAtom::Eq(fun("f", vec![var("X")]), fun("a", vec![]), true)
            ))
        );
        assert_eq!(
            atomic_formula("X != Y"),
            Ok(("", TptpAtom::Eq(var("X"), var("Y"), false)))
        );
        assert_eq!(
            atomic_formula("p => q"),
            Ok((" => q", TptpAtom::Pred("p".to_string(), vec![]))),
            "Atomic formula parser confuses `=>` with an equality"
        );
        assert!(
            atomic_formula("X").is_err(),
            "A variable is accepted as an atomic formula"
        );
    }
}
