//! Lexer: turns `&str` source into a `Vec<Token>`. See `token.rs` for the
//! token model and `scanner.rs` for the scanning implementation.

pub mod scanner;
pub mod token;

pub use scanner::lex;
pub use token::{Keyword, Sym, Token, TokenKind};
