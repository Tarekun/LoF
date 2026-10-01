#[cfg(test)]
mod unit_tests {
    use crate::tptp::syntax::{
        atomic_word, name, role, single_quoted, skip_annotations, ws0, Role,
    };

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
        assert_eq!(atomic_word(" p_1,"), Ok((",", "p_1".to_string())));
        assert!(
            atomic_word("X").is_err(),
            "Uppercase words are parsed as atomic words"
        );
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
            atomic_word("'Hello World'"),
            Ok(("", "Hello World".to_string()))
        );
        assert!(single_quoted("'unterminated").is_err());
    }

    #[test]
    fn test_roles() {
        assert_eq!(role("axiom"), Ok(("", Role::Axiom)));
        assert_eq!(
            role("negated_conjecture"),
            Ok(("", Role::NegatedConjecture))
        );
        assert_eq!(
            role("plain_ish"),
            Ok(("", Role::Other("plain_ish".to_string())))
        );
    }

    #[test]
    fn test_skip_annotations() {
        assert_eq!(
            skip_annotations(
                " inference(res, [status(thm)], [$fof(p & q)]) ). rest"
            ),
            Ok(("). rest", ())),
            "Annotation skipping doesnt stop at the closing parenthesis"
        );
        assert!(
            skip_annotations("file('a.p', [unbalanced").is_err(),
            "Annotation skipping accepts unbalanced brackets"
        );
    }
}
