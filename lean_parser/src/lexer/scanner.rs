//! The hand-written scanner: turns a `&str` into a `Vec<Token>`. See
//! `lexer::mod::lex` for the entry point and `token.rs` for the token
//! model this produces.

use crate::error::LeanError;
use crate::lexer::token::{
    is_id_continue, is_id_start, Keyword, Sym, Token, TokenKind, SYMBOLS,
};

/// Cursor over the source, tracking both a byte offset (for spans) and a
/// 1-based line / 0-based column counted in Unicode scalar values (`col`
/// is what the indentation-sensitive parts of the parser key off of, so
/// it must count codepoints, not bytes or grapheme clusters).
struct Scanner<'a> {
    src: &'a str,
    chars: Vec<(u32, char)>,
    idx: usize,
    line: u32,
    col: u32,
}

impl<'a> Scanner<'a> {
    fn new(src: &'a str) -> Scanner<'a> {
        let chars = src.char_indices().map(|(b, c)| (b as u32, c)).collect();
        Scanner {
            src,
            chars,
            idx: 0,
            line: 1,
            col: 0,
        }
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.idx).map(|(_, c)| *c)
    }

    fn peek_at(&self, k: usize) -> Option<char> {
        self.chars.get(self.idx + k).map(|(_, c)| *c)
    }

    fn byte_offset(&self) -> u32 {
        self.chars
            .get(self.idx)
            .map(|(b, _)| *b)
            .unwrap_or(self.src.len() as u32)
    }

    fn at_end(&self) -> bool {
        self.idx >= self.chars.len()
    }

    fn advance(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.idx += 1;
        if c == '\n' {
            self.line += 1;
            self.col = 0;
        } else {
            self.col += 1;
        }
        Some(c)
    }

    fn pos(&self) -> (u32, u32, u32) {
        (self.byte_offset(), self.line, self.col)
    }

    // -- comments -----------------------------------------------------

    /// Skips whitespace and non-doc comments; stops (without consuming)
    /// right before a `/--` doc comment so the caller can lex it as a
    /// real token. Returns whether a newline was crossed.
    fn skip_ws_and_comments(&mut self) -> Result<bool, LeanError> {
        let mut newline = false;
        loop {
            match self.peek() {
                Some(c) if c.is_whitespace() => {
                    if c == '\n' {
                        newline = true;
                    }
                    self.advance();
                }
                Some('-') if self.peek_at(1) == Some('-') => {
                    self.skip_line_comment();
                }
                Some('/') if self.peek_at(1) == Some('-') => {
                    // `/--` (doc comment) is lexed as a real token by the
                    // caller; `/-` and `/-!` (module doc) are both plain
                    // block comments as far as trivia-skipping cares.
                    if self.peek_at(2) == Some('-') {
                        break;
                    }
                    self.skip_block_comment()?;
                }
                _ => break,
            }
        }
        Ok(newline)
    }

    fn skip_line_comment(&mut self) {
        while let Some(c) = self.peek() {
            if c == '\n' {
                break;
            }
            self.advance();
        }
    }

    /// Consumes a `/- ... -/` block comment (already positioned at the
    /// opening `/`), honouring nesting: `/-` increments depth, `-/`
    /// decrements it, and the comment ends when depth returns to 0.
    fn skip_block_comment(&mut self) -> Result<(), LeanError> {
        let (start_off, start_line, start_col) = self.pos();
        self.advance();
        self.advance(); // consume '/-'
        let mut depth = 1i32;
        loop {
            match (self.peek(), self.peek_at(1)) {
                (None, _) => {
                    return Err(LeanError::lex(
                        "unterminated block comment",
                        start_off,
                        start_line,
                        start_col,
                    ))
                }
                (Some('/'), Some('-')) => {
                    depth += 1;
                    self.advance();
                    self.advance();
                }
                (Some('-'), Some('/')) => {
                    depth -= 1;
                    self.advance();
                    self.advance();
                    if depth == 0 {
                        break;
                    }
                }
                (Some(_), _) => {
                    self.advance();
                }
            }
        }
        Ok(())
    }

    /// Consumes a `/-- ... -/` doc comment (already positioned at the
    /// opening `/`), returning its content with the markers stripped and
    /// each line trimmed.
    fn scan_doc_comment(&mut self) -> Result<TokenKind, LeanError> {
        let (start_off, start_line, start_col) = self.pos();
        self.advance();
        self.advance();
        self.advance(); // consume '/--'
        let mut depth = 1i32;
        let mut content = String::new();
        loop {
            match (self.peek(), self.peek_at(1)) {
                (None, _) => {
                    return Err(LeanError::lex(
                        "unterminated doc comment",
                        start_off,
                        start_line,
                        start_col,
                    ))
                }
                (Some('/'), Some('-')) => {
                    depth += 1;
                    content.push('/');
                    self.advance();
                    content.push('-');
                    self.advance();
                }
                (Some('-'), Some('/')) => {
                    depth -= 1;
                    self.advance();
                    self.advance();
                    if depth == 0 {
                        break;
                    }
                    content.push('-');
                    content.push('/');
                }
                (Some(c), _) => {
                    content.push(c);
                    self.advance();
                }
            }
        }
        let trimmed = content
            .lines()
            .map(|l| l.trim())
            .collect::<Vec<_>>()
            .join("\n")
            .trim()
            .to_string();
        Ok(TokenKind::DocComment(trimmed))
    }

    // -- identifiers ----------------------------------------------------

    /// Consumes one identifier component: the current char (already
    /// known to satisfy `is_id_start`) plus a maximal run of
    /// `is_id_continue` characters.
    fn scan_ident_component(&mut self, buf: &mut String) {
        if let Some(c) = self.advance() {
            buf.push(c);
        }
        while let Some(c) = self.peek() {
            if is_id_continue(c) {
                buf.push(c);
                self.advance();
            } else {
                break;
            }
        }
    }

    fn scan_escaped_ident(&mut self) -> Result<TokenKind, LeanError> {
        let (start_off, start_line, start_col) = self.pos();
        self.advance(); // consume opening '«'
        let mut s = String::new();
        loop {
            match self.peek() {
                None => {
                    return Err(LeanError::lex(
                        "unterminated escaped identifier",
                        start_off,
                        start_line,
                        start_col,
                    ))
                }
                Some('»') => {
                    self.advance();
                    break;
                }
                Some(c) => {
                    s.push(c);
                    self.advance();
                }
            }
        }
        Ok(TokenKind::Ident(s))
    }

    /// Scans an identifier, keyword, or (for a lone `_`) the wildcard
    /// symbol. Dot-separated components (`Nat.succ`) collapse into a
    /// single `Ident`; keyword lookup only applies to undotted,
    /// single-component spellings (`Nat.def` stays an identifier).
    fn scan_ident_or_keyword(&mut self) -> Result<TokenKind, LeanError> {
        if self.peek() == Some('«') {
            return self.scan_escaped_ident();
        }
        let mut s = String::new();
        self.scan_ident_component(&mut s);
        loop {
            if self.peek() == Some('.')
                && self.peek_at(1).map_or(false, is_id_start)
            {
                self.advance(); // consume '.'
                s.push('.');
                self.scan_ident_component(&mut s);
            } else {
                break;
            }
        }
        if s == "_" {
            return Ok(TokenKind::Sym(Sym::Underscore));
        }
        if !s.contains('.') {
            if let Some(kw) = Keyword::from_str(&s) {
                return Ok(TokenKind::Keyword(kw));
            }
        }
        Ok(TokenKind::Ident(s))
    }

    fn scan_dot_ident(&mut self) -> Result<TokenKind, LeanError> {
        self.advance(); // consume '.'
        let mut s = String::new();
        self.scan_ident_component(&mut s);
        Ok(TokenKind::DotIdent(s))
    }

    fn scan_meta_ident(&mut self) -> Result<TokenKind, LeanError> {
        let (start_off, start_line, start_col) = self.pos();
        self.advance(); // consume '?'
        if !self.peek().map_or(false, is_id_start) {
            return Err(LeanError::lex(
                "expected an identifier after '?'",
                start_off,
                start_line,
                start_col,
            ));
        }
        let mut s = String::new();
        self.scan_ident_component(&mut s);
        Ok(TokenKind::MetaIdent(s))
    }

    // -- literals ---------------------------------------------------------

    fn scan_number(&mut self) -> Result<TokenKind, LeanError> {
        let (start_off, start_line, start_col) = self.pos();
        let mut raw = String::new();
        let radix = if self.peek() == Some('0')
            && matches!(self.peek_at(1), Some('x') | Some('X'))
        {
            raw.push(self.advance().unwrap());
            raw.push(self.advance().unwrap());
            16
        } else if self.peek() == Some('0')
            && matches!(self.peek_at(1), Some('b') | Some('B'))
        {
            raw.push(self.advance().unwrap());
            raw.push(self.advance().unwrap());
            2
        } else if self.peek() == Some('0')
            && matches!(self.peek_at(1), Some('o') | Some('O'))
        {
            raw.push(self.advance().unwrap());
            raw.push(self.advance().unwrap());
            8
        } else {
            10
        };
        let mut digits = String::new();
        while let Some(c) = self.peek() {
            if c == '_' {
                raw.push(c);
                self.advance();
                continue;
            }
            if c.is_digit(radix) {
                digits.push(c);
                raw.push(c);
                self.advance();
            } else {
                break;
            }
        }
        if digits.is_empty() {
            return Err(LeanError::lex(
                "expected digits in numeric literal",
                start_off,
                start_line,
                start_col,
            ));
        }
        let value = u64::from_str_radix(&digits, radix).map_err(|_| {
            LeanError::lex(
                "numeric literal out of range",
                start_off,
                start_line,
                start_col,
            )
        })?;
        Ok(TokenKind::Nat { value, raw })
    }

    fn scan_escape(&mut self) -> Result<char, LeanError> {
        let (start_off, start_line, start_col) = self.pos();
        match self.peek() {
            Some('n') => {
                self.advance();
                Ok('\n')
            }
            Some('t') => {
                self.advance();
                Ok('\t')
            }
            Some('r') => {
                self.advance();
                Ok('\r')
            }
            Some('\\') => {
                self.advance();
                Ok('\\')
            }
            Some('"') => {
                self.advance();
                Ok('"')
            }
            Some('\'') => {
                self.advance();
                Ok('\'')
            }
            Some('u') => {
                self.advance();
                if self.peek() != Some('{') {
                    return Err(LeanError::lex(
                        "expected '{' after \\u",
                        start_off,
                        start_line,
                        start_col,
                    ));
                }
                self.advance();
                let mut hex = String::new();
                while let Some(c) = self.peek() {
                    if c == '}' {
                        break;
                    }
                    hex.push(c);
                    self.advance();
                }
                if self.peek() != Some('}') {
                    return Err(LeanError::lex(
                        "unterminated unicode escape",
                        start_off,
                        start_line,
                        start_col,
                    ));
                }
                self.advance();
                let code = u32::from_str_radix(&hex, 16).map_err(|_| {
                    LeanError::lex(
                        "invalid unicode escape",
                        start_off,
                        start_line,
                        start_col,
                    )
                })?;
                char::from_u32(code).ok_or_else(|| {
                    LeanError::lex(
                        "invalid unicode escape",
                        start_off,
                        start_line,
                        start_col,
                    )
                })
            }
            Some(other) => Err(LeanError::lex(
                format!("unknown escape '\\{other}'"),
                start_off,
                start_line,
                start_col,
            )),
            None => Err(LeanError::lex(
                "unterminated escape sequence",
                start_off,
                start_line,
                start_col,
            )),
        }
    }

    fn scan_string(&mut self) -> Result<TokenKind, LeanError> {
        let (start_off, start_line, start_col) = self.pos();
        self.advance(); // consume opening '"'
        let mut s = String::new();
        loop {
            match self.peek() {
                None => {
                    return Err(LeanError::lex(
                        "unterminated string literal",
                        start_off,
                        start_line,
                        start_col,
                    ))
                }
                Some('"') => {
                    self.advance();
                    break;
                }
                Some('\\') => {
                    self.advance();
                    s.push(self.scan_escape()?);
                }
                Some(c) => {
                    s.push(c);
                    self.advance();
                }
            }
        }
        Ok(TokenKind::Str(s))
    }

    fn scan_char(&mut self) -> Result<TokenKind, LeanError> {
        let (start_off, start_line, start_col) = self.pos();
        self.advance(); // consume opening '\''
        let c = match self.peek() {
            None => {
                return Err(LeanError::lex(
                    "unterminated char literal",
                    start_off,
                    start_line,
                    start_col,
                ))
            }
            Some('\\') => {
                self.advance();
                self.scan_escape()?
            }
            Some(c) => {
                self.advance();
                c
            }
        };
        if self.peek() != Some('\'') {
            return Err(LeanError::lex(
                "unterminated char literal",
                start_off,
                start_line,
                start_col,
            ));
        }
        self.advance(); // consume closing '\''
        Ok(TokenKind::Char(c))
    }

    // -- attributes -------------------------------------------------------

    /// Scans `@[...]` as raw, unparsed text (balanced against nested
    /// `[`/`]`, and not confused by brackets inside a string literal).
    fn scan_attr(&mut self) -> Result<TokenKind, LeanError> {
        let (start_off, start_line, start_col) = self.pos();
        self.advance(); // '@'
        self.advance(); // '['
        let mut depth = 1i32;
        let mut s = String::new();
        loop {
            match self.peek() {
                None => {
                    return Err(LeanError::lex(
                        "unterminated attribute",
                        start_off,
                        start_line,
                        start_col,
                    ))
                }
                Some('"') => {
                    s.push('"');
                    self.advance();
                    loop {
                        match self.peek() {
                            None => {
                                return Err(LeanError::lex(
                                    "unterminated string in attribute",
                                    start_off,
                                    start_line,
                                    start_col,
                                ))
                            }
                            Some('"') => {
                                s.push('"');
                                self.advance();
                                break;
                            }
                            Some('\\') => {
                                s.push('\\');
                                self.advance();
                                if let Some(c) = self.peek() {
                                    s.push(c);
                                    self.advance();
                                }
                            }
                            Some(c) => {
                                s.push(c);
                                self.advance();
                            }
                        }
                    }
                }
                Some('[') => {
                    depth += 1;
                    s.push('[');
                    self.advance();
                }
                Some(']') => {
                    depth -= 1;
                    if depth == 0 {
                        self.advance();
                        break;
                    }
                    s.push(']');
                    self.advance();
                }
                Some(c) => {
                    s.push(c);
                    self.advance();
                }
            }
        }
        Ok(TokenKind::Attr(s))
    }

    // -- symbols ------------------------------------------------------

    /// Maximal-munch symbol matching against `SYMBOLS` (sorted
    /// longest-first): the first table entry that is a prefix of the
    /// remaining source is always the longest possible match.
    fn scan_symbol(&mut self) -> Result<TokenKind, LeanError> {
        let rest = &self.src[self.byte_offset() as usize..];
        for (spelling, sym) in SYMBOLS {
            if rest.starts_with(spelling) {
                for _ in 0..spelling.chars().count() {
                    self.advance();
                }
                return Ok(TokenKind::Sym(*sym));
            }
        }
        let (start_off, start_line, start_col) = self.pos();
        let c = self.peek().unwrap();
        Err(LeanError::lex(
            format!("unexpected character '{c}'"),
            start_off,
            start_line,
            start_col,
        ))
    }
}

/// Tokenizes `src` in full, returning the token stream terminated by a
/// single `Eof` sentinel (so every downstream error has a real
/// position, even one pointing past the last real token).
pub fn lex(src: &str) -> Result<Vec<Token>, LeanError> {
    let mut sc = Scanner::new(src);
    let mut out = Vec::new();
    loop {
        let newline_before = sc.skip_ws_and_comments()?;
        if sc.at_end() {
            let (off, line, col) = sc.pos();
            out.push(Token::new(
                TokenKind::Eof,
                off,
                off,
                line,
                col,
                newline_before,
            ));
            break;
        }
        let (start_off, start_line, start_col) = sc.pos();
        let c = sc.peek().unwrap();
        let kind = if c == '/'
            && sc.peek_at(1) == Some('-')
            && sc.peek_at(2) == Some('-')
        {
            sc.scan_doc_comment()?
        } else if c == '@' && sc.peek_at(1) == Some('[') {
            sc.scan_attr()?
        } else if c == '"' {
            sc.scan_string()?
        } else if c == '\'' {
            sc.scan_char()?
        } else if c.is_ascii_digit() {
            sc.scan_number()?
        } else if c == '?' {
            sc.scan_meta_ident()?
        } else if c == '.' && sc.peek_at(1).map_or(false, is_id_start) {
            sc.scan_dot_ident()?
        } else if c == '∀' {
            sc.advance();
            TokenKind::Keyword(Keyword::Forall)
        } else if c == '∃' {
            sc.advance();
            TokenKind::Keyword(Keyword::Exists)
        } else if is_id_start(c) {
            sc.scan_ident_or_keyword()?
        } else {
            sc.scan_symbol()?
        };
        let end_off = sc.byte_offset();
        out.push(Token::new(
            kind,
            start_off,
            end_off,
            start_line,
            start_col,
            newline_before,
        ));
    }
    Ok(out)
}

#[cfg(test)]
mod unit_tests {
    use super::*;
    use crate::lexer::token::TokenKind::*;

    fn kinds(src: &str) -> Vec<TokenKind> {
        lex(src).unwrap().into_iter().map(|t| t.kind).collect()
    }

    #[test]
    fn dotted_identifier_is_one_token() {
        assert_eq!(kinds("Nat.succ"), vec![Ident("Nat.succ".to_string()), Eof]);
    }

    #[test]
    fn dot_number_splits_into_three_tokens() {
        // `x.1` is not a projection in scope; the lexer must not corrupt
        // it into a dotted identifier -- '.' followed by a digit is not
        // an identifier start, so this stays `x`, `.`, `1`.
        assert_eq!(
            kinds("x.1"),
            vec![
                Ident("x".to_string()),
                Sym(crate::lexer::token::Sym::Dot),
                Nat {
                    value: 1,
                    raw: "1".to_string()
                },
                Eof
            ]
        );
    }

    #[test]
    fn keyword_lookup_skips_dotted_and_multi_component_names() {
        // `Nat.def` must stay an identifier: keyword lookup only
        // applies to undotted, single-component spellings.
        assert_eq!(kinds("Nat.def"), vec![Ident("Nat.def".to_string()), Eof]);
        assert_eq!(
            kinds("def"),
            vec![Keyword(crate::lexer::token::Keyword::Def), Eof]
        );
    }

    #[test]
    fn subscript_letters_continue_identifiers() {
        assert_eq!(kinds("h₁"), vec![Ident("h₁".to_string()), Eof]);
    }

    #[test]
    fn escaped_identifier_allows_spaces() {
        assert_eq!(
            kinds("«a weird name»"),
            vec![Ident("a weird name".to_string()), Eof]
        );
    }

    #[test]
    fn lone_underscore_is_wildcard_symbol() {
        assert_eq!(
            kinds("_"),
            vec![Sym(crate::lexer::token::Sym::Underscore), Eof]
        );
    }

    #[test]
    fn underscore_prefixed_identifier_stays_an_identifier() {
        assert_eq!(kinds("_foo"), vec![Ident("_foo".to_string()), Eof]);
    }

    #[test]
    fn nested_block_comments_match_correctly() {
        // The whole comment is skipped; only the trailing `x` survives.
        assert_eq!(
            kinds("/- outer /- inner -/ still outer -/ x"),
            vec![Ident("x".to_string()), Eof]
        );
    }

    #[test]
    fn doc_comment_beats_plain_block_comment() {
        assert_eq!(
            kinds("/-- a doc comment -/"),
            vec![DocComment("a doc comment".to_string()), Eof]
        );
    }

    #[test]
    fn module_doc_comment_is_skipped_like_a_plain_comment() {
        assert_eq!(
            kinds("/-! module doc -/ x"),
            vec![Ident("x".to_string()), Eof]
        );
    }

    #[test]
    fn unterminated_block_comment_errors_at_opening_position() {
        let err = lex("/- never closed").unwrap_err();
        match err {
            LeanError::Lex { line, col, .. } => {
                assert_eq!((line, col), (1, 0));
            }
            other => panic!("expected Lex error, got {other:?}"),
        }
    }

    #[test]
    fn unterminated_string_errors() {
        let err = lex("\"never closed").unwrap_err();
        assert!(matches!(err, LeanError::Lex { .. }));
    }

    #[test]
    fn maximal_munch_prefers_longer_symbols() {
        assert_eq!(
            kinds("<;>"),
            vec![Sym(crate::lexer::token::Sym::SeqFocus), Eof]
        );
        assert_eq!(kinds("<"), vec![Sym(crate::lexer::token::Sym::Lt), Eof]);
        assert_eq!(
            kinds(":="),
            vec![Sym(crate::lexer::token::Sym::ColonEq), Eof]
        );
        assert_eq!(kinds(":"), vec![Sym(crate::lexer::token::Sym::Colon), Eof]);
    }

    #[test]
    fn line_comment_after_expression() {
        assert_eq!(
            kinds("x -- trailing comment\ny"),
            vec![Ident("x".to_string()), Ident("y".to_string()), Eof]
        );
    }

    #[test]
    fn column_counts_codepoints_not_bytes() {
        // '∀' is a 3-byte UTF-8 sequence but a single codepoint; the
        // token after it must be at column 2 (codepoints), not 4 (bytes).
        let toks = lex("∀ y").unwrap();
        assert_eq!(toks[1].col, 2, "column must count codepoints, not bytes");
    }

    #[test]
    fn newline_before_is_tracked_per_token() {
        let toks = lex("x\ny").unwrap();
        assert!(!toks[0].newline_before);
        assert!(toks[1].newline_before);
    }

    #[test]
    fn eof_sentinel_is_always_appended() {
        let toks = lex("x").unwrap();
        assert_eq!(toks.last().unwrap().kind, Eof);
    }

    #[test]
    fn line_col_advance_across_newlines() {
        let toks = lex("x\n  y").unwrap();
        assert_eq!((toks[1].line, toks[1].col), (2, 2));
    }
}
