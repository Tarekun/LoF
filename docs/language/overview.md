# LoF Language Overview

LoF (Language of Formulas) is a proof assistant implemented in Rust. It supports proof checking, proof automation, and logic programming through a multi-type-system architecture. Rather than committing to one type theory, LoF is designed around a trait-based interface that allows multiple type systems to coexist and be selected at runtime via configuration.

## Capabilities

- **Proof checking**: Write proofs as terms (proof-as-programs via Curry-Howard) or interactively via tactics. CIC is the primary system for this.
- **Proof automation**: Automatically find proofs using the saturation algorithm. SUP handles this at the logical level.
- **Logic programming**: Model a domain in First-Order Logic and let the engine solve queries automatically. FOL compiles down to SUP for this purpose.

## Type Systems

| System | Full Name | Primary Purpose |
|--------|-----------|-----------------|
| CIC | Calculus of Inductive Constructions | Proof checking, dependent types |
| FOL | First-Order Logic | Expressive interface to proof automation |
| SUP | Superposition Calculus | Automatic theorem proving via saturation |
| STLC | Simply Typed Lambda Calculus | Legacy, unsupported |

CIC is the default and most complete system. FOL acts as a higher-level layer over SUP. SUP is not directly accessible to users — it is the backend that FOL compiles into.

## Project Structure

```
language/
  src/
    parser/          # Nom-based parser, AST definition
    type_theory/
      interface.rs   # Core traits for type systems
      environment.rs # Shared environment (context, deltas, predicates, constructors)
      commons/       # Algorithms generic across all type systems
      cic/           # Calculus of Inductive Constructions
      fol/           # First-Order Logic
      sup/           # Superposition Calculus
      stlc/          # Simply Typed Lambda Calculus (legacy)
    runtime/         # Program execution and entry points
    error.rs         # LofError, the shared error type for the whole pipeline
    config.rs        # Configuration loading
    cli.rs           # Small CLI arg-parsing helper (get_flag_value)
    main.rs          # Entry point dispatch: parses argv, selects the type system
library/             # Standard library (.lof files)
```

## Execution Pipeline

Every piece of LoF code goes through these stages in order:

1. **Parsing** — source files are read and turned into a system-agnostic AST (`LofAst`)
2. **Elaboration** — the AST is mapped to the term/type representation of the configured type system
3. **Type checking** — type system-specific rules validate the elaborated program
4. **Execution** — statements are evaluated, updating the environment (adding definitions, verifying theorems)

See [architecture.md](architecture.md) for the full data flow.
