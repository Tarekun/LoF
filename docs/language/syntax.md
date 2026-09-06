# Language Syntax

LoF source files use the `.lof` extension. This page documents the full surface syntax with examples from the standard library.

## Comments

A `#` starts a comment that runs to the end of the line.

```
# This is a comment
```

At the top level, a comment on its own line is parsed as a standalone `Statement::Comment()` node. But comments are not only a whole-line, top-level construct: `#...` is skipped anywhere the parser accepts whitespace (`ws0`/`ws1` in `language/src/parser/commons.rs`), which is most of the surface syntax — between arguments, inside `match` arms, between binders, etc. So comments can appear nested inside composite expressions, not just as standalone lines, e.g. (`library/tests/expressions/match.lof`):

```
match n with
| z => z,             # 0->0
| s(z) => z,          # 1->0
| s(s(z)) => z,       # 2->0
| s(nn) => s(z),      # else->1
```

## Expressions

### Variables

```
x
Nat
TYPE
PROP
```

### Lambda Abstraction

```
\lambda x: T. body
```

The `∀` (or `\forall`) keyword is an alias for lambda in expression position. In type position it becomes a universal quantifier/dependent product.

### Function Application

```
f(a, b, c)
```

Arguments are a parenthesized, comma-separated list (a trailing comma is allowed), collected into a single `Application` node — there is no space-juxtaposition application. This is uniform across the language: ordinary function calls, predicate/type applications, and constructor patterns inside `match` all use this same form:

```
le(z, n)
Eq(T, x, x)
And(P, Q)
cons(h, l)
```

At least one argument is required; a nullary constructor or function is referenced bare (as a plain variable), e.g. `z` (`Nat`'s zero constructor) rather than `z()`.

### Arrow Types (non-dependent)

```
Nat -> Nat
A -> B -> C   # right-associative: A -> (B -> C)
```

### Dependent Product (Π-type)

```
\Pi x: A. B(x)
∀x: A. B(x)
```

When the body `B` does not depend on `x`, this is equivalent to `A -> B`.

### Match Expression

```
match term with
| pattern1 => body1,
| pattern2 => body2,
```

Each branch ends with a trailing comma. Patterns are constructor applications, using the same parenthesized, comma-separated syntax as any other application, e.g. (`library/nat.lof`):

```
fun pred (n: Nat) : Nat {
  match n with
  | z => z,
  | s(nn) => nn,
}
```

### Let Binding

```
let x : T := body; scope
let x := body; scope   # type is inferred
```

Note there is no `in` keyword — the definition and its scope are separated by `;`.

### Inference Wildcard

```
?
```

Elaborated to a fresh metavariable. The engine will attempt to infer the correct term from context. (A plain `_` is not this wildcard — it is an ordinary identifier, conventionally used as a bound variable name for a pattern component the branch body ignores, e.g. `cons(?, _, ll)` in `library/lists.lof`.)

### Tuple and Pipe

```
(a, b, c)   # conjunctive tuple
a | b | c   # disjunctive union
```

## Statements

### Axiom

Asserts a proposition without proof. Adds the name to the context.

```
axiom name : formula;
```

Example:
```
axiom Nat : TYPE;
axiom z : Nat;
axiom s : Nat -> Nat;
```

### Global Definition

Defines a named constant with an optional type annotation.

```
global name : type := body;
global name := body;
```

### Function Definition

```
fun name (arg1: T1, arg2: T2) : ReturnType {
  body
}

fun rec name (arg: T) : ReturnType {
  body   # name is in scope here for recursion
}
```

The parameter list is a single parenthesized, comma-separated group (empty parentheses may be omitted for a zero-parameter function). `fun rec` enables structural recursion. The function name is added as a local assumption with its full type during body checking.

Example (`library/nat.lof`):
```
fun rec plus (n: Nat, m: Nat) : Nat {
  match n with
  | z => m,
  | s(nn) => s(plus(nn, m)),
}
```

### Inductive Type Definition

```
inductive TypeName (param1: P1, param2: P2) : Arity {
  | constructor1: ConstructorType1
  | constructor2: ConstructorType2
}
```

As with function parameters, the parameter list is a single parenthesized, comma-separated group, and may be omitted entirely when the type has no parameters.

Example (`library/nat.lof`, `library/lists.lof`):
```
inductive Nat: TYPE {
  | z: Nat
  | s: Nat -> Nat
}

inductive List (T:TYPE) : TYPE {
  | nil : List(T)
  | cons : T -> List(T) -> List(T)
}

inductive le : Nat -> Nat -> PROP {
  | lez: ∀n: Nat. le(z, n)
  | les: ∀n:Nat. ∀m:Nat. le(n, m) -> le(s(n), s(m))
}
```

After elaboration, the type name and all constructor names are added to the environment as separate axioms.

### Theorem

`theorem`, `lemma` and `proposition` are interchangeable keyword aliases for the same statement.

Two proof styles are supported.

**Term proof** (Curry-Howard):
```
theorem name : Formula := proof_term
```

**Tactic proof** (interactive):
```
theorem name : Formula :=
  begin
  tactic1
  tactic2
  qed.
```

Example (`library/tests/proofs/basic_tactics.lof`):
```
theorem zero_plus_one_term : Eq(Nat, plus(z, s(z)), s(z)) := (refl(Nat, s(z)))

theorem zero_plus_one_tac : Eq(Nat, plus(z, s(z)), s(z)) :=
  begin
  exact refl(Nat, s(z))
  qed.
```

### Tactics

| Tactic | Syntax | Effect |
|--------|--------|--------|
| `begin` | `begin` | Opens the tactic block |
| `exact` | `exact expr` | Closes the current goal with `expr` |
| `intro` | `intro x [: T]` | Introduces variable `x` when goal is `∀x:T.P`; the `: T` annotation is optional (defaults to inferring `T`) |
| `apply` | `apply f` | Applies `f` to the current goal, generating subgoals for its arguments |
| `qed` | `qed.` | Closes the tactic block |

### Equivalence

Declares that two types are equivalent, bundling the data needed to
transport proofs and definitions between them. See
[systems/transport.md](systems/transport.md) for what each field means.

```
equivalence <Name> : <TypeA> <-> <TypeB> {
  forward    := <expr>;      # f : A -> B
  backward   := <expr>;      # g : B -> A
  section    := <expr>;      # forall a:A. g(f(a)) = a
  retraction := <expr>;      # forall b:B. f(g(b)) = b
  dep_elim   := <expr>;      # eliminator over B shaped like A's own
  eta        := <expr>;      # optional
  dep_constr {
    | <A_constructor> => <expr>
    ...
  }
  iota {
    | <A_constructor> => <expr>
    ...
  }
}
```

The two types are named without their parameters (`List`, not `List(T)`).
Fields are parsed in the order shown; only `eta` may be omitted. Example
(`library/tests/proofs/transport_nat_bin.lof`):

```
equivalence NatBin : Nat <-> Bin {
  forward    := nat_to_bin;
  backward   := bin_to_nat;
  section    := section_nat_bin;
  retraction := retraction_nat_bin;
  dep_elim   := bin_succ_induction;
  dep_constr {
    | z => bz
    | s => bin_succ
  }
  iota {
    | z => refl(Bin, bz)
    | s => bin_succ_correct
  }
}
```

### Transport

Rewrites an already-checked `theorem`, or an existing `fun`/`global`, into
its counterpart over the equivalent type.

```
transport <new_name> : <new_type_or_formula> from <old_name> using <equiv_name>;
```

The target type is mandatory. Whether the result is registered as a theorem
or as a definition follows from its sort (`PROP` ⇒ theorem). Transporting a
definition also records the name mapping, so proofs transported afterwards
pick it up - so auxiliary functions must be transported before the proofs
that call them.

```
transport plus_bin : Bin -> Bin -> Bin from plus using NatBin;
```

### Auto (FOL only)

Instructs the engine to automatically prove `formula` via saturation:

```
auto formula;
```

The current environment's axioms are compiled to clauses and SUP is run.

### Solve (FOL only)

Logic programming query — asks whether `formula` holds, optionally computing witnesses:

```
solve formula
```

Multiple comma-separated goals are also accepted (`solve formula1, formula2, …`). Example (from `library/tests/loprog/nat.lof`):
```
solve NatEq(plus(s(z), r), s(s(s(z))))
```

The engine runs saturation and binds query variables (like `r`) to their computed values.

### HClause (Horn Clause)

Expresses a Prolog-style Horn clause, with `<-` separating the head from an optional comma-separated list of subgoals:

```
hclause head <- subgoal1, subgoal2, …;
```

Or as a fact with no subgoals:
```
hclause head;
```

Example, matching `le`'s inductive definition above:
```
hclause le(z, n);
hclause le(s(n), s(m)) <- le(n, m);
```

## Custom Notation (Sugar)

Register user-defined infix/prefix/postfix notations with positional holes `_0`, `_1`, …:

```
sugar "pattern" := "expansion"
```

Notations are tried in the order they were declared (first-declared, first-tried) and are attempted before ordinary application parsing, so a notation is not shadowed by a call that happens to start with the same identifier.

Examples (`library/nat.lof`):
```
sugar "_0 + _1" := "plus(_0, _1)"
sugar "_0 - _1" := "minus(_0, _1)"
sugar "_0 * _1" := "times(_0, _1)"
```

After registration, `n + m` is parsed as `plus(n, m)`.

## Theory Blocks

Lock specific definitions to a type system:

```
!theory_block cic
  inductive Nat: TYPE { … }
!end_block
```

Definitions outside a theory block use the globally configured type system. This allows mixing CIC inductive types with FOL functions in the same file.

## File and Directory Structure

A workspace can be a single `.lof` file or a directory. When given a directory, LoF discovers all `.lof` files and parses them as a `DirRoot` containing one `FileRoot` per file.

### Import

```
import "modname"
```

Recursively parses `modname.lof` and splices its `FileRoot` in place at the point of the `import` — there is no dedicated `Import` AST node. Used throughout the standard library, e.g. `import "unit"` in `library/bool.lof` and `import "nat"` in `library/lists.lof`.

The `# include "logic"` comment form (not yet implemented) was an earlier, aspirational spelling for the same idea; since it starts with `#` it parses today as an ordinary comment and has no effect:
```
# include "logic"
```
