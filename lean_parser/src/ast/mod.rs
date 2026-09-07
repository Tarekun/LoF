//! The parsed AST. `term.rs` covers expressions/binders/patterns,
//! `decl.rs` covers modules/declarations, `tactic.rs` covers tactics.
//!
//! Every node is a struct pairing a `#[serde(flatten)]`-ed, internally
//! tagged `*Kind` enum with a `span: Span`, e.g.
//! `{"kind":"app","func":{...},"args":[...],"span":{...}}`. This
//! imposes one hard constraint everywhere in this module: **every enum
//! variant must be a struct variant** (`Foo { a, b }`), never a newtype
//! variant (`Foo(T)`) -- with `#[serde(tag = "kind")]`, a newtype
//! variant wrapping a non-map value serializes to a bare scalar and
//! `flatten` panics at runtime. This is exercised by a serde
//! round-trip test per variant in each of the three submodules.

pub mod decl;
pub mod tactic;
pub mod term;

pub use decl::{Ctor, Decl, DeclKind, Modifiers, Module};
pub use tactic::{Tactic, TacticKind};
pub use term::{
    Binder, BinderInfo, MatchAlt, Pattern, PatternKind, SortKind, Term,
    TermKind,
};
