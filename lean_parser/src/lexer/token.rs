//! Token and TokenKind definitions, plus the keyword/symbol tables used
//! by the scanner (`scanner.rs`) for maximal-munch matching.

use serde::Serialize;

/// One lexical token. Byte offsets are into the original `&str` source;
/// `line`/`col` locate the token's *first* character (1-based line,
/// 0-based column counted in Unicode scalar values, matching Lean's own
/// convention -- not bytes, not grapheme clusters).
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct Token {
    pub kind: TokenKind,
    pub start: u32,
    pub end: u32,
    pub line: u32,
    pub col: u32,
    /// True when the whitespace/comments skipped immediately before this
    /// token contained at least one newline. This is the only piece of
    /// "layout" information the lexer records beyond raw column -- it is
    /// what lets the parser tell a same-line `by exact foo` apart from a
    /// `let x := e` whose body starts on the next line (see
    /// `parser::commons` and the indentation-sensitivity notes in the
    /// plan/README).
    pub newline_before: bool,
}

impl Token {
    pub fn new(
        kind: TokenKind,
        start: u32,
        end: u32,
        line: u32,
        col: u32,
        newline_before: bool,
    ) -> Token {
        Token {
            kind,
            start,
            end,
            line,
            col,
            newline_before,
        }
    }

    /// The literal source text this token spans (used for `Unknown`
    /// tactic bodies, doc-comment attachment, and diagnostics).
    pub fn text<'a>(&self, src: &'a str) -> &'a str {
        &src[self.start as usize..self.end as usize]
    }
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum TokenKind {
    /// Possibly dot-separated: `Nat`, `Nat.succ`, `List.map`, or an
    /// escaped identifier `«weird id»` (stored without the guillemets).
    Ident(String),
    /// A leading-dot identifier: `.succ`, `.mk` (stored without the
    /// leading `.`). These are Lean's anonymous-constructor-style dotted
    /// names, e.g. `.z`/`.s n` when the expected type is known.
    DotIdent(String),
    /// `?m`, `?_` -- a synthetic-hole/metavariable name (stored without
    /// the leading `?`).
    MetaIdent(String),
    Nat {
        value: u64,
        raw: String,
    },
    Str(String),
    Char(char),
    Keyword(Keyword),
    Sym(Sym),
    /// `/-- ... -/` content, with the `/--`/`-/` markers stripped and
    /// each line's leading whitespace trimmed. Not skipped like ordinary
    /// comments -- attached to the following declaration.
    DocComment(String),
    /// `@[simp, inline]` captured whole as raw text (without the
    /// `@[`/`]` delimiters); recorded verbatim, never parsed further.
    Attr(String),
    /// Always the last token in a stream, positioned at end-of-input, so
    /// every parse error has a real position even past the last real
    /// token.
    Eof,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub enum Keyword {
    Def,
    Abbrev,
    Theorem,
    Lemma,
    Example,
    Axiom,
    Inductive,
    Import,
    Fun,
    Forall,
    Exists,
    Let,
    Have,
    Match,
    With,
    By,
    Where,
    Then,
    Else,
    If,
    Type,
    Prop,
    Sort,
    Partial,
    Private,
    Protected,
    Unsafe,
    Noncomputable,
    Deriving,
}

impl Keyword {
    /// Undotted-identifier spellings that lex as this keyword. Order
    /// doesn't matter here (unlike `SYMBOLS`) since keyword lookup is a
    /// map, not a scan.
    pub fn from_str(s: &str) -> Option<Keyword> {
        use Keyword::*;
        Some(match s {
            "def" => Def,
            "abbrev" => Abbrev,
            "theorem" => Theorem,
            "lemma" => Lemma,
            "example" => Example,
            "axiom" => Axiom,
            "inductive" => Inductive,
            "import" => Import,
            "fun" => Fun,
            "forall" | "\\forall" => Forall,
            "exists" | "\\exists" => Exists,
            "let" => Let,
            "have" => Have,
            "match" => Match,
            "with" => With,
            "by" => By,
            "where" => Where,
            "then" => Then,
            "else" => Else,
            "if" => If,
            "Type" => Type,
            "Prop" => Prop,
            "Sort" => Sort,
            "partial" => Partial,
            "private" => Private,
            "protected" => Protected,
            "unsafe" => Unsafe,
            "noncomputable" => Noncomputable,
            "deriving" => Deriving,
            _ => return None,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub enum Sym {
    // binders / structure
    Arrow,      // -> / →  (also the return-type arrow in binder groups)
    MapsTo,     // => / ↦
    Colon,      // :
    ColonEq,    // :=
    Semi,       // ;
    Comma,      // ,
    Dot,        // .
    DotDot,     // ..
    Bar,        // |
    Underscore, // _  (the wildcard pattern, not part of an identifier)
    At,         // @  (bare, not part of an `@[...]` attribute)
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    LAngle,     // ⟨
    RAngle,     // ⟩
    LStrictImp, // ⦃
    RStrictImp, // ⦄
    SeqFocus,   // <;>

    // operators
    Iff,    // <-> / ↔
    And,    // /\  / ∧
    Or,     // \/  / ∨
    Not,    // ¬
    Eq,     // =
    Ne,     // != / ≠
    Le,     // <= / ≤
    Lt,     // <
    Ge,     // >= / ≥
    Gt,     // >
    Add,    // +
    Sub,    // -
    Mul,    // *
    Div,    // /
    Mod,    // %
    Pow,    // ^
    Append, // ++
    Cons,   // ::
    Comp,   // ∘
    Prod,   // ×
    Sum,    // ⊕
}

/// Symbol spellings, longest-first so the scanner's maximal-munch loop
/// (`scanner.rs`) always prefers the longer match (`<;>` before `<`,
/// `:=` before `:`, `++` before `+`, etc). `unit_tests` below asserts
/// this table really is sorted by descending length.
pub const SYMBOLS: &[(&str, Sym)] = &[
    ("<->", Sym::Iff),
    ("<;>", Sym::SeqFocus),
    (":=", Sym::ColonEq),
    ("=>", Sym::MapsTo),
    ("->", Sym::Arrow),
    ("!=", Sym::Ne),
    ("<=", Sym::Le),
    (">=", Sym::Ge),
    ("++", Sym::Append),
    ("::", Sym::Cons),
    ("/\\", Sym::And),
    ("\\/", Sym::Or),
    ("..", Sym::DotDot),
    ("↔", Sym::Iff),
    ("↦", Sym::MapsTo),
    ("→", Sym::Arrow),
    ("∧", Sym::And),
    ("∨", Sym::Or),
    ("¬", Sym::Not),
    ("≠", Sym::Ne),
    ("≤", Sym::Le),
    ("≥", Sym::Ge),
    ("∘", Sym::Comp),
    ("×", Sym::Prod),
    ("⊕", Sym::Sum),
    ("⟨", Sym::LAngle),
    ("⟩", Sym::RAngle),
    ("⦃", Sym::LStrictImp),
    ("⦄", Sym::RStrictImp),
    (":", Sym::Colon),
    (";", Sym::Semi),
    (",", Sym::Comma),
    (".", Sym::Dot),
    ("|", Sym::Bar),
    ("_", Sym::Underscore),
    ("@", Sym::At),
    ("(", Sym::LParen),
    (")", Sym::RParen),
    ("{", Sym::LBrace),
    ("}", Sym::RBrace),
    ("[", Sym::LBracket),
    ("]", Sym::RBracket),
    ("=", Sym::Eq),
    ("<", Sym::Lt),
    (">", Sym::Gt),
    ("+", Sym::Add),
    ("-", Sym::Sub),
    ("*", Sym::Mul),
    ("/", Sym::Div),
    ("%", Sym::Mod),
    ("^", Sym::Pow),
];

/// Identifier-continue predicate: `XID_Continue` plus the extra
/// characters Lean allows in identifiers -- `'` (prime, e.g. `h'`), and
/// subscript/superscript-ish letters used for variable naming
/// (`h₁`, `xₙ`, `aⁱ`) that Unicode classifies outside `XID_Continue`.
pub fn is_id_continue(c: char) -> bool {
    unicode_xid::UnicodeXID::is_xid_continue(c)
        || c == '\''
        || c == '!'
        || ('\u{2080}'..='\u{2089}').contains(&c) // subscript digits
        || ('\u{2090}'..='\u{209C}').contains(&c) // subscript letters
        || ('\u{1D62}'..='\u{1D6A}').contains(&c) // subscript letters (Latin, IPA ext)
}

/// Identifier-start predicate: `XID_Start` plus `_` (Lean allows
/// leading underscores) and the escaped-identifier opener `«`.
pub fn is_id_start(c: char) -> bool {
    unicode_xid::UnicodeXID::is_xid_start(c) || c == '_' || c == '«'
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    #[test]
    fn symbols_table_is_sorted_longest_first() {
        for w in SYMBOLS.windows(2) {
            assert!(
                w[0].0.chars().count() >= w[1].0.chars().count(),
                "SYMBOLS must be sorted by descending length so maximal \
                 munch works: {:?} came before {:?}",
                w[0].0,
                w[1].0
            );
        }
    }

    #[test]
    fn keyword_lookup_only_matches_known_spellings() {
        assert_eq!(Keyword::from_str("def"), Some(Keyword::Def));
        assert_eq!(Keyword::from_str("definitely"), None);
        assert_eq!(Keyword::from_str("Nat"), None);
    }

    #[test]
    fn id_continue_accepts_primes_and_subscripts() {
        assert!(is_id_continue('\''));
        assert!(is_id_continue('₁'));
        assert!(is_id_continue('a'));
        assert!(!is_id_continue(' '));
        assert!(!is_id_continue('('));
    }

    #[test]
    fn id_start_accepts_underscore_and_escaped_open() {
        assert!(is_id_start('_'));
        assert!(is_id_start('«'));
        assert!(is_id_start('x'));
        assert!(!is_id_start('1'));
    }
}
