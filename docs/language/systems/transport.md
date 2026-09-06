# Transport across type equivalences

`language/src/type_theory/cic/transport.rs`,
`language/src/type_theory/commons/transport.rs`

Transport takes a proof or definition stated in terms of one type and
mechanically rewrites it into the corresponding proof or definition about an
equivalent type. It is aimed at *proof repair*: when a datatype's
representation changes, the developments built on it don't have to be
rewritten by hand.

## Theoretical basis

For the theory this rests on - what a configuration *is*, why Iota and Eta
are the two components that need machinery, why Eta had to be definitional
and why that forces the no-indices condition, and a reading list -
see [transport-theory.md](transport-theory.md). The summary:

The implementation follows Ringer, Porter, Yazdani, Leo & Grossman,
[*Proof Repair across Type Equivalences*](https://arxiv.org/abs/2010.00774)
(the PUMPKIN Pi tool for Coq). That approach transforms proof **terms**
directly, guided by a per-equivalence *configuration* with four components:

| Component | Meaning | Here |
|---|---|---|
| **DepConstr** | how each constructor of the source type is built on the target side | `dep_constr` table |
| **DepElim** | the eliminator to use over the target type in place of the source type's own | `dep_elim` field |
| **Eta** | repackaging needed when the target type bundles extra data | supplied by the kernel's own eta rule for single-constructor inductives; the `eta` field is recorded but no longer needed |
| **Iota** | proofs bridging steps that reduce definitionally on the source side but only propositionally on the target | `iota` table, one entry per source constructor |

Crucially the approach needs **no new axioms**: the output is an ordinary
term checked by the ordinary kernel. That is what makes it implementable
here as a language feature rather than a kernel redesign.

### Why this approach and not another

Two other families were considered and rejected for this codebase:

- **Statement-level transfer** (Isabelle/HOL's Transfer package;
  [Coq's `transfer` plugin](https://arxiv.org/pdf/1505.05028)) rewrites a
  *goal* along a registered isomorphism and discharges a fresh obligation by
  composing with it. It never inspects proof terms, so it cannot carry over
  computational content - only opaque propositions.
- **Univalent parametricity** and its generalization *Trocq* translate the
  whole type theory through a parametricity/logical-relations construction,
  needing either the univalence axiom or a bespoke hierarchy of relations
  inside the kernel. Far more general, but a kernel redesign: this CIC has
  no universe hierarchy and no relational infrastructure to build on.

The 2023 follow-up on *quotient* type equivalences needs setoid rewriting as
an oracle and loses the axiom-free property outside Cubical Agda; quotients
are out of scope here.

## Surface syntax

### Declaring an equivalence

```
equivalence <Name> : <TypeA> <-> <TypeB> {
  forward    := <expr>;      # f : A -> B
  backward   := <expr>;      # g : B -> A
  section    := <expr>;      # forall a:A. g(f(a)) = a
  retraction := <expr>;      # forall b:B. f(g(b)) = b
  dep_elim   := <expr>;      # eliminator over B, shaped like A's own
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

`<TypeA>`/`<TypeB>` are bare type names; a parameterized type is named
without its parameters (`List`, not `List(T)`). Fields are parsed in the
order shown. A value may be any expression - typically a name defined
earlier, or a parenthesized `\lambda`.

`dep_elim` must accept the same argument shape as the *source* type's
generated eliminator `e_<TypeA>`: parameters, motive, one case per
constructor of A, then the target. That is what lets the engine drop it in
wherever the source proof eliminated an A.

Each `iota` entry is `dep_elim`'s *propositional computation rule* at the
corresponding DepConstr - what `dep_elim` would reduce to at that
constructor, stated as an equation because in general it does not reduce
there:

```
iota[c] : forall params. forall C. forall case_1..case_n. forall a_1..a_k.
  Eq( C(dep_constr_c(a..)),
      dep_elim(params, C, case_1..case_n, dep_constr_c(a..)),
      case_c(a.., dep_elim(params, C, case.., a_rec) ..) )
```

The table may be left empty when `dep_elim` genuinely computes, as
`ListPackedVec`'s does - the engine only reaches for an entry when a
transported case does not already type check.

### Invoking transport

```
transport <new_name> : <new_type_or_formula> from <old_name> using <equiv_name>;
```

`<old_name>` may be a checked `theorem`, or a `fun`/`global`. Whether the
result is registered as a new theorem or as a new definition is decided by
the sort of `<new_type_or_formula>` (`PROP` ⇒ theorem-shaped). The target
type is mandatory: there is deliberately no "translate the statement
automatically" pass, that being the statement-level approach this design
does not adopt.

Transporting a `fun`/`global` also records `old_name -> new_name` in the
equivalence, so later transports of proofs that *call* it pick up the new
name automatically. Auxiliary functions must therefore be transported
before the proofs that use them.

## How the engine works

`transport_term` walks the source term structurally:

| Node | Action |
|---|---|
| a constructor of `type_a` (bare or applied) | replaced by its `dep_constr` image, arguments transported |
| an application of `e_<type_a>` | head replaced by `dep_elim`, arguments (motive, cases, target) transported, minor premises repaired via `iota` where needed |
| a name already lifted under this equivalence | replaced by its lifted counterpart |
| an occurrence of `type_a` itself | replaced by `type_b` |
| `Abstraction`/`Product` | binder type and body transported - this is what turns `forall x:A. …` into `forall x:B. …`, with no separate statement-translation pass |
| a raw `match` over `type_a` | rejected (see Limitations) |

`transport_definition` handles the one shape the structural walk cannot: a
`fun rec`-style body whose top level is a `match` on a `type_a`-typed
parameter. That `match` is converted into a `dep_elim` application - a
constant motive built from the declared target type, one minor premise per
constructor built from the corresponding branch, and each self-recursive
call replaced by the induction hypothesis.

Each transported minor premise is then checked against the type `dep_elim`
expects of it. When it already matches, nothing happens - which is why an
equivalence with an empty `iota` table behaves exactly as before. When it
does not, the constructor's `iota` entry is instantiated by first-order
matching against the goal and used to rewrite it, via `e_Eq` (this kernel's
J). The rewrite eliminates once, into a function
`abstracted[to] -> goal`, rather than composing a `sym` with a rewrite:
type checking a curried application re-checks its whole function spine, so
nesting multiplies rather than adds.

Two vocabularies meet at that point. The rule speaks about `dep_elim`
applied at a DepConstr image; the goal says the same thing by calling the
lifted function built from it. Matching therefore runs against a scratch
copy with the lifted names unfolded, while the rewrite is applied back in
the goal's own folded vocabulary - emitting normal forms instead would
inline every definition the goal mentions, which measured two orders of
magnitude more type-check work.

The result is re-indexed, type checked with the ordinary kernel, and unified
against the declared target type before being registered. A failed
transport therefore surfaces as an ordinary type error - the kernel remains
the only thing that decides what is a proof.

## Worked examples

Both live in `library/tests/proofs/` and run as part of `cargo test`.

### Unary ≃ binary naturals (`transport_nat_bin.lof`)

`Nat` (`z`/`s`) against a binary representation mirroring Coq's own
`N`/`positive` split. `s`'s DepConstr image is `bin_succ`, an ordinary
function rather than a constructor of `Bin` - exactly the mismatch that
motivates DepConstr. `dep_elim` is `bin_succ_induction`, which has to be
*derived*: `e_Bin`'s own `bp` case takes a `Pos`, not a recursive `Bin`, so
it cannot express "prove `C(bin_succ(b))` from `C(b)`". It is bootstrapped
by induction on `Nat` (where `nat_to_bin(s(n)) = bin_succ(nat_to_bin(n))`
holds definitionally) and then transferred to `Bin` via the retraction.

`transport plus_bin … from plus` succeeds, and `plus_z_r` transports on top
of it. That last step is what needs Iota: `plus_z_r`'s base case is `refl`,
a proof only because `plus(z,z)` computes to `z`, while `plus_bin(bz,bz)`
does not compute to `bz` at all - `bin_succ_induction` is a derived theorem
routed through an axiomatized retraction, so it has no computational
behaviour. The two `iota` entries supply that equality, and the engine
rewrites both the base and the step case along them.

Those two entries are themselves axiomatized, alongside the
`retraction_nat_bin` the fixture already assumed. Deriving them needs a
`bin_succ_induction` that genuinely computes - Coq's `Pos.peano_rect`,
defined by direct structural recursion on `Pos` rather than bootstrapped
through the retraction - plus its `peano_rect_succ` lemma: a
binary-arithmetic development on the scale of Coq's own standard library.
The List/PackedVec example below needs no axiom at all.

### Lists ≃ length-indexed vectors (`transport_list_vec.lof`)

`List(T)` against `PackedVec(T)`, a `Vec(T,n)` bundled with its length
(the paper's `Σ n. vector n`, spelled as a one-constructor inductive since
this language has no dependent pair). `dep_elim` is an ordinary `global`
composing the two generated eliminators `e_PackedVec` and `e_Vec`, so unlike
the Nat/Bin case it computes. Both `len` and `app` transport into functions
over `PackedVec`, and so does the theorem `len_app_nil` about them.

The theorem is the case that needs Eta. `len(cons(h,l))` reduces
definitionally, but `pv_cons` - `cons`'s DepConstr image - is a function
that must destructure its argument, and for the universally quantified `pv`
an induction's step case introduces, that `match` is stuck. The kernel's
eta rule unsticks it: `PackedVec` has a single constructor, so every `pv`
*is* a `pack`. Nothing in the equivalence declaration changes to make this
work - the configuration was already sufficient, `iota` stays empty, and
the transported proof uses no axiom.

## Kernel changes this required

Transport is a language feature, but making it work exposed gaps in the
kernel that had never been exercised - nothing in the codebase had used a
generated eliminator before, so no proof by induction had ever been checked.
The following were fixed along the way:

- **ι-reduction for generated eliminators.** `e_<Type>` applications had a
  type but no computation rule, so anything defined through an eliminator
  never reduced, even on a concrete constructor.
  `try_reduce_eliminator_application` supplies it, including for indexed
  families.
- **Reduction under binders.** Normalization never descended into a
  `Product`/`Abstraction`, so two Pi-types differing only by an
  under-binder redex - the routine case when comparing an eliminator's
  generated types - were never recognized as equal.
- **A stuck `match` is a normal form**, not a panic: a scrutinee that is an
  open variable is exactly what an inductive proof's step case produces.
- **Substitution round-trips through unification.** Solved substitutions
  keyed by an ordinary variable (rather than a metavariable) were fed to a
  metavariable-only substitution function, panicking on the key.
- **Pattern variables are binding occurrences.** Constraint collection
  type-checked them as if they were references, so any term containing a
  `match` failed the moment its enclosing abstraction was checked.
- **Identity bindings.** `x ≐ x` where only one side is flagged global (an
  artifact of indexing each elaborated fragment separately) was reported as
  an occurs-check cycle.
- **Eta for single-constructor inductives.** A `match` or `e_<Type>` whose
  target is an opaque value of a one-constructor type was permanently
  stuck. It now eta-expands into `C(params.., t.0, .., t.k-1)`, the fields
  being a new `Proj` term former. `Proj` has to be its own term former
  rather than sugar for an `e_<Type>` application: an eliminator-encoded
  projection would itself be a stuck eliminator application, so the rule
  would fire on its own output and expand forever, and normalization has no
  fuel. Eligibility is three conditions - exactly one constructor, **no
  indices**, and no recursive occurrence among the constructor's arguments.
  The middle one is soundness, not caution: `Eq` is single-constructor, and
  eta for it would say every proof of `Eq(T,x,y)` is `refl`, ie hand out
  UIP/axiom K.
- **Application type checking is no longer exponential.** Checking an
  application collected unification constraints over the whole `f x` term,
  and constraint collection on an application itself type checks that
  application's function - the two were mutually recursive, so cost doubled
  per argument. Only the node's own constraint (the argument's type against
  the domain) is collected now; both sides have just been type checked in
  their own right. A six-argument curried application nested three deep
  went from 27 million type-check calls to a few hundred, and the whole
  test suite from 20s to 15s while doing strictly more work.
- **Un-reduced function and scrutinee types.** A dependent eliminator's
  result type is literally `motive(target, proof)`, so a term whose type
  comes from one arrives as a beta-redex rather than a `Pi` or an inductive
  instance. Application checking, `match` checking and constraint
  collection now normalize on that fallback path.
- **Theorem proof terms are retained.** `evaluate_theorem` discarded them,
  so an already-proved theorem's witness could not be retrieved by name -
  which transport fundamentally needs.

## Limitations

These are the boundaries of the MVP. Where one is pinned by a fixture, it
lives under `library/tests/transport_failures/` and is asserted to fail by
`test_transport_expected_failures`.

**Iota entries are hand-written, and may need axioms.** The engine consumes
the `iota` table but does not derive it. Where `dep_elim` computes, the
table can be empty; where it does not, each entry is a proof obligation the
library author owes, and one that can be genuinely hard - see the Nat/Bin
example above, whose entries are axiomatized rather than derived.

**Eta covers single-constructor, index-free, non-recursive types only.**
Those are the conditions the kernel rule requires (see above; the
no-indices one is what keeps `Eq` out, and with it UIP). A target type
outside them whose DepConstr images must destructure their own recursive
argument will still get stuck, and no `iota` entry can help - the
stuck-ness is in an ordinary function, not in `dep_elim`.

**One rewrite per premise.** A minor premise is repaired by a single
rewrite along a single `iota` entry, located by first-order matching. A
case needing two independent bridging steps, or one whose redex is not an
instance of any declared rule, falls through to an ordinary type error.

**Raw `match` over the source type.** (`raw_match.lof`.) Only a top-level
recursion split is converted to `dep_elim`. A `match` elsewhere is rejected
rather than rewritten, because the source type's constructors need not
correspond to constructors of the target type at all - rewriting the
patterns through DepConstr would produce a `match` whose patterns aren't
constructors. Source proofs should eliminate via `e_<Type>` explicitly.

**No automatic configuration discovery.** Every `dep_constr`, `dep_elim` and
`iota` entry is written by hand. The paper's own search heuristics are
limited to four built-in procedures and frequently need manual override; not
attempting them keeps the engine's behaviour predictable.

**Recursion shape.** `transport_definition` handles structural recursion on
one parameter where each self-recursive call passes the recursive sub-term
(in any argument position) with the other arguments unchanged. Mutual
recursion, recursion nested under a second `match`, and calls whose other
arguments are themselves transformed are out of scope.

**Auxiliary lifting is not transitive.** The engine does not walk a
function's call graph and lift dependencies on demand; each must be
transported first, bottom-up. Doing it automatically risks non-termination
when the target refines the source, a hazard the paper also flags.

**No mutual or nested inductive types**, and **no quotient types** - both
are pre-existing gaps in this kernel rather than transport-specific ones.

**No decompiler.** PUMPKIN Pi can render a transported term back into a
tactic script (explicitly forfeiting soundness to do so); this produces only
kernel-checked terms.

### Two practical gotchas

- **Bound-variable names must be distinct across nested scopes.** The
  unifier keys variables by name, so reusing a name that a motive or an
  inductive's parameter already binds produces spurious failures. The
  fixtures rename accordingly (`bx`, `Tp`).
- **Deeply nested proof terms are expensive.** Normalization recurses
  through a term's structure, so a large proof is cheaper split into named
  lemmas than written as one deep term - `transport_nat_bin.lof` extracts
  `double_s` and `pos_succ_correct_xI` for exactly this reason.
