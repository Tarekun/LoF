# Bug hunt log

This file tracks bugs found while writing new `.lof` programs against the
current standard library and exercising currently-supported language
features, in the style of the existing regression files under
`library/tests/`. Each entry documents the symptom, the root cause, the fix,
and how it was verified.

## 1. Tactic-mode proofs were never checked against the theorem's stated formula

**Symptom:** A `theorem ... := begin ... qed.` proof was accepted as long as
the final assembled proof term type-checked to *some* type - it was never
verified to have the type actually stated by the theorem. For example (before
the fix), the following was accepted:

```
axiom P : PROP;
axiom Q : PROP;
axiom pq : P -> Q;
axiom p : P;

theorem bogus : Q :=
  begin
  apply pq
  exact p
  qed.
```

which happens to be a *true* implication, so it's not by itself alarming -
but the same missing check meant a proof of the wrong premises, or of an
unrelated fact, could slip through undetected as long as each individual
tactic step happened to be locally well-typed (see bugs #2 and #3 below for
concrete cases this masked).

**Root cause:** `type_check_theorem_base` (in
`language/src/type_theory/commons/type_check.rs`) computes
`are_compatible(&proof_type, formula, environment)` for the tactic-mode
branch, but the result was discarded - the `if` body was empty apart from a
`TODO` comment: *"figure out what to do in this branch ... should it fail or
require refinement?"*. The equivalent check in the term-mode (`theorem name :
Formula := proof_term`) branch, immediately above it, does return an error on
mismatch, so tactic-mode and term-mode proofs were inconsistently checked.

**Fix:** Made the tactic-mode branch return `LofError::type_mismatch` on
incompatibility, symmetric with the term-mode branch.

**Verification:** Enabling this check surfaced two more, previously-masked
bugs (see below); once those were also fixed, all 169 tests pass including
the new regression test (`test_apply_multi_premise_subgoal_order` in
`language/src/runtime/entrypoints.rs`) and the full standard library still
type-checks and executes cleanly.

## 2. `apply`'s subgoals were solved in the wrong order for multi-premise lemmas

**Symptom:** `apply`-ing a lemma with more than one premise required
discharging the premises with `exact`/`apply` in the *reverse* of their
declared order to be accepted - and, combined with bug #1, discharging them
in their natural declared order was *rejected* while the reversed (wrong)
order was silently accepted.

```
axiom pq2 : P -> P2 -> Q;
...
theorem q_from_two_premises : Q :=
  begin
  apply pq2
  exact p    # P is pq2's first premise ...
  exact p2   # ... and P2 is its second
  qed.
```
This natural ordering used to fail with a unification error, while swapping
the two `exact` lines made it pass.

**Root cause:** `type_check_interactive_proof`'s `solver` (in
`language/src/type_theory/commons/type_check.rs`) keeps pending subgoals in a
`Vec` used as a stack (`.pop()` to fetch the next one). When a tactic step
produced more than one new subgoal (eg. `apply` on a lemma with two
premises), they were pushed with `subgoals.extend(new_subgoals)` in their
declared, left-to-right order - which means `.pop()` (LIFO) would hand them
back out in the *reverse* of that order.

**Fix:** Reverse the newly produced subgoals before pushing them
(`subgoals.extend(new_subgoals.into_iter().rev())`), so `.pop()` yields them
in their original declared order while still preserving the (correct)
existing behaviour of resolving a step's own new subgoals before any
older, still-pending ones.

**Verification:** New test `test_apply_multi_premise_subgoal_order` in
`language/src/runtime/entrypoints.rs` asserts the declared order is accepted
and the reversed order is rejected. New regression file
`library/tests/proofs/apply_multi_premise.lof` exercises the same scenario
end-to-end (parsed, elaborated, type-checked and executed by
`test_dedicated_scripts`).

## 3. `swap_proof_hole` collapsed the whole partial proof instead of filling in a single hole

**Symptom:** Once bug #2's ordering was accounted for, `apply`-ing a
multi-premise lemma still produced a *wrong* final proof term: each `exact`
step, instead of plugging its proof into the correct argument slot of the
partially-applied lemma, replaced the *entire* partial proof built so far -
silently discarding the applied lemma. Eg. for `apply pq2; exact p; exact
p2`, the final "proof" of `Q` ended up being just the term `p2` (of type
`P2`), not `Application(Application(pq2, p), p2)` (of type `Q`). This was
invisible before bug #1 was fixed, since the final proof term's type was
never compared against the stated formula.

**Root cause:** `swap_proof_hole` (in
`language/src/type_theory/cic/cic_utils.rs`) matched on `Application(_, _)`
(and, more subtly, `Variable(_, _)` and any `Sort(_)`, not just the specific
hole sentinel) and returned `new_body` unconditionally - treating *any*
already-built application node as if it *were* the hole to replace, rather
than recursing into it to find the actual hole placeholder
(`Sort("THIS_IS_A_PARTIAL_PROOF_HOLE")`) still nested inside it. Compounding
this, `type_check_apply` only ever introduced a single hole
(`Application(lemma, Cic::proof_hole())`) regardless of how many premises the
applied lemma had, so there was nowhere for a second premise's proof to go
even if the traversal had been correct.

**Fix:**
- `type_check_apply` (in `language/src/type_theory/cic/tactics.rs`) now
  builds one fresh hole per premise via the already-existing
  `apply_arguments` helper, applying the lemma to `premises.len()` distinct
  holes instead of exactly one.
- `swap_proof_hole` now only replaces an exact match of the hole sentinel,
  and otherwise recurses structurally (into an `Abstraction`'s body, or -
  left branch first, then right - into an `Application`'s two sides),
  returning `None` up the call chain when a subtree contains no hole so a
  sibling branch can be tried instead. This also correctly supports several
  simultaneously-pending holes (eg. from a multi-premise `apply`), always
  filling in the leftmost one first, which lines up with the subgoal order
  fixed in bug #2.

**Verification:** Same tests as bug #2 - the final assembled proof term is
now type-checked (bug #1) against the stated formula and only passes when it
is actually `Application(Application(pq2, p), p2) : Q`, not merely typeable
as something. Existing `swap_proof_hole` unit tests in `cic_utils.rs` (single
and nested `Abstraction`s from consecutive `intro`s) continue to pass
unchanged.

## 4. Tactic proofs mixed inconsistent variable-binding metadata across steps

**Symptom:** Once bug #1's check was enabled, an *existing*, previously
"passing" (because unchecked) regression file,
`library/tests/proofs/intro_apply_tactics.lof`, started failing with
`Type mismatch ... expected Πn:Nat|G. ... n|0 ... n|0, found ... n|G ... n|G`
- i.e. a perfectly correct `intro`+`exact` proof of `∀n:Nat. Eq(Nat, n, n)`
was rejected because its reconstructed type disagreed with the stated
formula only in how the bound variable `n` was tagged internally.

**Root cause:** LoF's CIC terms tag variables either with a proper,
depth-relative de Bruijn index (for variables bound by an enclosing
`Abstraction`/`Product` in the *same* elaboration pass) or with a sentinel
"global" index (for anything looked up by name in the environment, eg.
axioms or - as it turns out - tactic-introduced assumptions). Tactic steps
are each elaborated and checked independently, one subgoal at a time
(`intro` adds the new assumption to the environment by name only, and marks
its occurrences in the next subgoal with the global index so it isn't
accidentally treated as a solvable metavariable - see the `// TODO: see
issue #286` note in `type_check_intro`), then glued together into one
`Abstraction` at the end. The *stated* formula, by contrast, was elaborated
in one pass from source, so its bound variable keeps a proper relative
index. Once the final proof term is assembled, both representations refer to
the same variable, but aren't structurally equal, and CIC's equality check
does (rightly, in general) distinguish differently-indexed variables.

**Fix:** Added `Interactive::reindex_proof` to the type-theory interface
(`language/src/type_theory/interface.rs`), implemented for CIC by re-running
the existing `index_variables` pass (already used right after ordinary
expression elaboration) over the fully assembled tactic proof term, and as a
no-op for FOL (which does not support tactics). This normalizes the finished
proof term's variable tags to what ordinary, single-pass elaboration would
have produced before it is type-checked against the theorem's formula.
`type_check_theorem_base` now calls it right after assembling an interactive
proof.

**Verification:** `library/tests/proofs/intro_apply_tactics.lof` (and the
rest of the `intro`/`apply` regression suite) passes again with the bug #1
check enabled; all 169 tests in `cargo test` pass.

## 5. A bare lambda couldn't be passed directly as a function argument

**Symptom:** `f(\lambda x: T. body)` failed to parse at all (`Unparsed
remainder starting at: ...`), even though a lambda is an ordinary
expression and `f(x, y, z)`-style application accepts "any expression" as an
argument per the docs. The only way to pass a function literal was to wrap
it in an extra, otherwise-meaningless pair of parens:
`f((\lambda x: T. body))` - which is exactly what every use of `if(...)` in
`library/bool.lof` already does (`if(?, true, (\lambda i: Unit. false),
(\lambda i: Unit. true))`), suggesting this had already been discovered and
silently worked around rather than fixed.

**Root cause:** `argument_expression` (in `language/src/parser/expressions.rs`,
used for each comma-separated slot inside `f(...)`) only tried `parse_custom`,
`parse_app`, `parse_var`, `parse_meta` and `parse_parens` as alternatives -
never a bare abstraction (`parse_abs`) or forall (`parse_type_abs`), unlike
the top-level `parse_expression`, which tries both before anything else.
`parse_app` looks like it should have covered a lambda too (its `left` side,
`applicable_expression`, does include `parse_abs`/`parse_type_abs`) but
`parse_app` additionally *requires* a following `(args)` list to actually be
an application; a lambda used as a plain, non-applied argument has no such
trailing parens, so `parse_app` fails and there was nothing left in the
`alt(...)` to fall back on.

**Fix:** Added `parse_abs` and `parse_type_abs` as the first alternatives
tried in `argument_expression`, mirroring `parse_expression`'s order.

**Verification:** New parser unit test
`test_application_accepts_bare_lambda_argument` in
`language/src/tests/parser/expressions.rs`, plus new end-to-end regression
file `library/tests/expressions/lambda_argument.lof` (which also exercises
bug #6 below, since it applies a lambda literal through a higher-order
function).

## 6. Substituting a variable could cross into a shadowing inner binder

**Symptom:** Passing a lambda literal as an argument to a function whose own
body reused the lambda's bound variable name for something else silently
computed the *wrong* value instead of erroring - the most direct example
being a generic `apply_twice(f, n) { f(f(n)) }` called with a lambda
argument that itself takes a parameter also named `n`:

```
fun rec apply_twice (f: Nat -> Nat, n: Nat) : Nat {
  f(f(n))
}

# silently reduced to `s(z)` instead of `s(s(z))`
theorem apply_lambda_twice :
  Eq(Nat, apply_twice(\lambda n: Nat. s(n), z), s(s(z))) := (refl(Nat, s(s(z))))
```
Only reusing the same parameter name across the two functions triggers it -
the exact same program with the lambda's parameter renamed to anything else
computes the correct answer, and using a *named* function instead of an
inline lambda for the same purpose works fine either way (both sidestep the
buggy code path, see below).

**Root cause:** `substitute` (in `language/src/type_theory/cic/cic_utils.rs`)
recursed into an `Abstraction`/`Product`'s codomain unconditionally, even
when that binder's own `var_name` was identical to the `target_name` being
substituted - i.e. even when the inner binder *shadows* the substituted
variable. The `Let` case immediately below it already special-cased this
correctly (skipping the substitution in `scope` when `var_name ==
target_name`, with a comment noting `scope`'s name is overridden), and there
was even a pre-existing `// TODO: dont carry substitution if names match to
implement overriding of names` comment directly on the `Abstraction` arm -
but the fix was never made.
Concretely: reducing `apply_twice(lambda_arg, z)` first substitutes
`apply_twice`'s `f` parameter with `lambda_arg` inside its body
`\lambda n: Nat. f(f(n))`, giving `\lambda n: Nat. lambda_arg(lambda_arg(n))`
- so far correct. Reducing this applied to `z` then substitutes `n` with
`z`, but since `lambda_arg` is itself `\lambda n: Nat. s(n)`, the buggy,
unconditional recursion reached *inside* both copies of `lambda_arg` and
also replaced *their* own (shadowing, unrelated) `n` with `z`, turning them
into `\lambda n: Nat. s(z)` (a lambda that ignores its argument). The
resulting, corrupted term reduces to `s(z)` instead of `s(s(z))`.

**Fix:** Mirrored `Let`'s existing handling: `substitute` now only recurses
into an `Abstraction`/`Product`'s codomain when `var_name != target_name`;
the domain (evaluated in the outer scope, so never shadowed by its own
binder) is still always substituted.

**Verification:** New unit test
`test_substitute_does_not_cross_a_shadowing_binder` in
`language/src/type_theory/cic/cic_utils.rs`, directly exercising the shadowing
case, the domain-still-substitutes case, and the genuinely-free-still-
substitutes case. End-to-end coverage via
`library/tests/expressions/lambda_argument.lof` (bug #5's regression file,
which happens to exercise this exact shadowing scenario) and the standalone
`ho2`/`ho3`/`ho4`/`ho5` variants used to isolate the bug during
investigation (single application, two independent nested calls, and a
named-function equivalent all already worked correctly, narrowing the bug
down to substitution specifically). All 171 tests in `cargo test` pass.

## 7. `apply` couldn't be used on a parametrized inductive constructor at all

**Symptom:** Proving `Or(P, Q)`/`And(P, Q)`-shaped goals via `apply` on their
own constructors - about the most ordinary thing to do with `Or`/`And`/etc.
- failed outright, in three different ways depending on details:

```
inductive Or (P: PROP, Q: PROP) : PROP {
  | left: P -> Or(P, Q)
  | right: Q -> Or(P, Q)
}
axiom P : PROP;
axiom Q : PROP;
axiom p : P;

theorem or_via_apply : Or(P, Q) :=
  begin
  apply left
  exact p
  qed.
```
- With the caller's own axioms named differently from `Or`'s parameters
  (eg. `Foo`/`Bar` instead of `P`/`Q`), this either crashed the whole process
  with `thread 'main' panicked ... ParseIntError` or, depending on order of
  fixes, asked the next tactic step to prove the nonsensical goal `PROP`.
- With the caller's own axioms named the *same* as the constructor's
  parameters (`P`, `Q`, as above - an extremely natural thing to do, and
  exactly what every predicate in `library/logic.lof` does with its own
  callers) it instead failed with a plain `do not unify` error before
  `apply` even got to pick premises.

This is a chain of four separate, compounding bugs, all needed together to
make ordinary `apply` usage on parametrized constructors work at all:

**7a. Constructor field types never got their own parameters' occurrences
properly bound.** `elaborate_inductive` (`language/src/type_theory/cic/elaboration.rs`)
elaborates each constructor's field type (eg. `P -> Or(P, Q)`) on its own,
before the inductive's declared parameters (`P`, `Q`) exist as enclosing
binders in that expression - so any reference to them is elaborated as an
unbound/global variable. The parameters' `Product`s are only wrapped around
the field type *afterwards*, by `make_multiarg_fun_type`, in
`evaluate_inductive`/`type_check_inductive` - which never re-derives the
now-properly-nested variables' binding metadata. The result: a constructor's
own parameter references stay permanently tagged as free/global, making them
structurally indistinguishable from an unrelated global constant, so
unification (which is what `apply`'s subgoal generation relies on, unlike
ordinary name-based substitution) could never solve for them.
Fix: `evaluate_inductive` now runs the existing `index_variables` pass over
the fully-wrapped inductive type and each fully-wrapped constructor type
before registering them, so their parameters are correctly bound the same
way any other elaborated `Π`-chain's are.

**7b. Solving a plain (non-metavariable) variable during unification
crashed.** Once (7a) made such a variable solvable, `solve_unifications_unnormalized`'s
final substitution-reduction step (`language/src/type_theory/cic/unification.rs`)
only handled `metavariable_<idx>`-keyed solutions (via `substitute_meta`),
and unconditionally tried to `.parse()` any other key as an integer index -
panicking with `ParseIntError` on the `variable_<name>`-keyed solutions
`is_substitutable` also produces for plain bound variables.
Fix: handle both key shapes, applying `substitute` by name for the latter.

**7c. `apply` never propagated a solved parameter into the remaining
premises.** `type_check_apply` only checked `Cic::type_unify(target,
conclusion).is_ok()`, discarding the solving substitution entirely, then
returned *all* of the lemma's premises via `get_arg_types` unmodified - so
premises whose value the unification had just determined (a constructor's
own type parameters) were still handed to the user as new subgoals, and
`PROP`/`TYPE`-sorted premises like these can never be "proven" as if they
were propositions.
Fix: `type_check_apply` now keeps the substitution, and (using the new
`get_named_arg_types` to keep each premise's binder name) fills in any
premise whose name the substitution solved directly as a concrete argument,
substituting the solution into the type of only the genuinely remaining
premises, which alone become new subgoals - mirroring how `apply`/`eapply`
behave in mainstream interactive provers.

**7d. The occurs-check compared candidates by display name only.** Even
after (7a)-(7c), solving `variable_P := <the caller's own axiom P>`
specifically (as opposed to some other, differently-named term) was rejected
by `occurs_var_check` (`language/src/type_theory/cic/unification.rs`) as a
bogus self-reference, since it matched `Variable(var_name, _) => var_name ==
name` regardless of whether that variable was the caller's own unrelated
global constant or a genuine occurrence of the local variable being solved.
Fix: also require the candidate not be a global constant
(`*dbi != GLOBAL_INDEX`), matching the same distinction `is_substitutable`
already uses to decide what counts as solvable in the first place.

**Verification:** New regression file
`library/tests/proofs/apply_parametrized_constructor.lof` (exercising `Or`
and `And`, with the caller's axioms deliberately named the same as the
constructors' own parameters, `P`/`Q`, to cover 7d). New unit tests
`test_apply_solves_leading_bound_parameters_via_unification` (in
`language/src/type_theory/cic/tactics.rs`) and
`test_cic_occurs_ignores_a_global_constant_sharing_the_variable_name` (in
`language/src/tests/type_theory/cic/unification.rs`). All 173 tests in
`cargo test` pass, and the whole standard library still type-checks and
executes cleanly.

**Known remaining limitation (not fixed):** `apply`-ing a constructor whose
premises depend on an earlier, *value-level* (not type-level) parameter that
doesn't itself appear in the conclusion - eg. `Exists`'s `excon : ∀t:T. P(t)
-> Exists(T, P)`, where using it to prove `Exists(Nat, λn. Eq(Nat, n, z))`
needs to pick a witness `t` that only the *next* tactic step actually
provides - still fails (`Unification error: ... and Nat do not unify`).
Fixing this needs the missing premise to become an actual metavariable
(`?`) threaded through the remaining subgoals, so a later step's choice of
witness can retroactively specialize an earlier, dependent premise's type;
the current subgoal-tracking model (a flat, upfront list of already-concrete
premise types) has no room for that. This is an existing, larger piece of
machinery (metavariable-based goal-directed elaboration), not something to
bolt on as a small patch, so it's documented here rather than attempted.

## 8. An incomplete tactic proof was silently accepted as complete

**Symptom:** Running out of tactic steps while a subgoal was still pending
didn't reject the proof - it was accepted, and the failure only surfaced
later as a confusing, implementation-detail error:

```
theorem le_refl_like : ∀n: Nat. le(n, n) :=
  begin
  intro n : Nat
  qed.
```
(an incomplete proof - `intro` alone only peels off the `∀`, it doesn't
discharge the resulting `le(n, n)` subgoal) failed with:
```
Program failed: Unbound variable: THIS_IS_A_PARTIAL_PROOF_HOLE
```
- naming the tactic engine's own internal hole-placeholder sentinel, not
anything about the actual proof.

**Root cause:** `type_check_interactive_proof`'s `solver`
(`language/src/type_theory/commons/type_check.rs`) matched on the remaining
tactic list *after* already confirming `subgoals` was non-empty, but its `[]`
(no tactics left) arm returned `Ok(partial_proof)` unconditionally - exactly
the gap flagged by an adjacent `// TODO: make sure the proof closes with a
qed.` comment. The returned term still had `Interactive::proof_hole()`'s
sentinel (`Sort("THIS_IS_A_PARTIAL_PROOF_HOLE")`) embedded wherever the
missing tactic step would have filled it in, which only failed later, when
that sentinel reached ordinary type-checking and was treated like any other
unrecognized `Variable`.

**Fix:** The `[]` arm now returns a `LofError` naming the count and content
of the still-pending subgoals, instead of silently succeeding.

**Verification:** New unit test
`test_u_type_check_theorem_rejects_incomplete_tactic_proof` (in
`language/src/tests/type_theory/commons/type_check.rs`), checking both that
an incomplete proof is now rejected with a clear message and that the same
formula is still accepted once every subgoal is actually discharged. All 174
tests in `cargo test` pass.

## 9. Custom notations can't be mixed in the same expression (documented, not fixed)

**Symptom:** Two independently-registered custom notations (`sugar`) parse
fine on their own, but not combined in the same expression:

```
sugar "_0 + _1" := "plus(_0, _1)"
sugar "_0 * _1" := "times(_0, _1)"

theorem precedence_check : Eq(Nat, s(z) + s(s(z)) * s(s(z)), s(s(s(z)))) := ...
```
fails to parse (`Unparsed remainder ...`), even though `s(z) + s(z)` and
`s(z) * s(z)` each parse fine alone, and the same expression parses fine
once the mixed part is wrapped in redundant parens:
`s(z) + (s(s(z)) * s(s(z)))`.

**Root cause:** `parse_custom` (`language/src/parser/expressions.rs`) parses
each notation's `_N` placeholder via `non_custom_expression`, which
deliberately excludes `parse_custom` from its own alternatives (hence the
name) to avoid unbounded left-recursion (a placeholder re-invoking notation
matching against the very same input position it's currently mid-match on).
The consequence: a notation's operand can never itself be *another*
notation's application - so parsing `+`'s right-hand operand on `s(s(z)) *
s(s(z))` stops at `s(s(z))` (the longest match `non_custom_expression` can
produce without recognizing `*`), leaving `* s(s(z))` dangling and
unconsumed, which then breaks the enclosing parse.

**Why this is documented rather than fixed:** naively adding `parse_custom`
to `non_custom_expression`'s alternatives reintroduces exactly the
unbounded left-recursion it was written to avoid (parsing `*`'s own `_0`
placeholder on `s(s(z)) * s(s(z))` would immediately retry every notation,
including `*` again, on that same starting position - a stack overflow, not
a fix). A real fix needs actual precedence-climbing (per-notation binding
powers, Pratt-parser style) so nesting is resolved deterministically instead
of by whichever alternative happens to be tried first; a shortcut that lets
notations nest without one would silently pick *some* precedence/
associativity for every pair of registered notations (most likely always
right- or left-associating them in registration order, regardless of what a
reader would expect from `+`/`*`), which is arguably worse than the current
hard parse error - it would silently produce whichever parse tree the
implementation happens to build rather than the one the notations'
declared precedence (if any existed) would call for. Since `library/nat.lof`
only ever uses one arithmetic notation per expression today, this hasn't
surfaced there, but it blocks the very next natural line of standard-library
code (a lemma or example mixing `+` and `*` in one expression, eg.
distributivity). Flagging it here rather than shipping a partial fix that
would trade a loud parse error for a silently wrong parse tree.

## 10. A diamond import hung the whole process

**Symptom:** Writing a file that imports two library modules which
themselves share a common dependency - an extremely ordinary thing to do in
any multi-file project, eg. wanting both `nat`'s arithmetic and `lists`'s
list operations (`lists` itself already `import`s `nat`) - made the process
spin at 100% CPU forever instead of type checking:

```
import "nat"
import "lists"

theorem len_check :
  Eq(Nat, len(cons(Nat, z, nil(Nat))), s(z)) :=
  (refl(Nat, s(z)))
```
(plus an `import "logic"` for `Eq`/`refl`, or an inline definition). Merely
importing both without ever using anything from them was fine; the hang
only appeared once something involving the resulting, duplicated
environment was actually evaluated (eg. calling the recursive `len`).

**Root cause:** `import` (`parse_import` in
`language/src/parser/statements.rs`) unconditionally re-parses and splices
the target module's *entire* contents on every single `import` statement
that names it, with no tracking of what had already been imported. A
diamond import (`zzz` importing both `nat` and `lists`, and `lists` itself
importing `nat`) therefore spliced `nat.lof`'s definitions twice just from
resolving `zzz`'s own two `import`s, stacking duplicate registrations for
every name in it on top of each other in the environment. This duplication
compounds with every further shared import, and evaluating a recursive
function over the resulting doubly/triply-redefined environment was
observed to never terminate - each of `library/nat.lof` and
`library/lists.lof` on their own already gets this kind of light
duplication today (both are themselves top-level library files *and*
`lists.lof` separately `import`s `nat`), which is apparently harmless in
isolation, but the same pattern compounds badly once more than one shared
import contributes further duplicate layers.

**Fix:** `LofParser` now tracks which module paths have already been
imported (`imported_modules`, a `RefCell<HashSet<String>>` alongside the
existing `custom_notations` interior-mutable parser state). `parse_import`
now checks this set first and, if the target was already imported, returns
a no-op `Statement::Comment()` instead of re-parsing and re-splicing it -
standard "include guard" semantics, matching what `import` should have been
doing all along for repeated/diamond imports.

**Verification:** New parser unit test `test_import_is_deduplicated` (in
`language/src/tests/parser/statements.rs`), checking that a first import
actually splices content while a second import of the same module returns
the no-op `Comment()`. Manually re-reproduced the hang in an isolated
scratch workspace (copies of `nat.lof`/`lists.lof`/`logic.lof` plus a file
importing all three) before the fix (reliably hangs past a 20s timeout) and
confirmed it resolves instantly after; not captured as a `library/tests/`
`.lof` file since none of the existing ones use `import` (its relative-path
resolution depends on the process's current working directory, which
differs between running the whole `library/` workspace and running a single
file under `library/tests/`, unlike everything else in that directory,
which is self-contained). All 175 tests in `cargo test` pass, and the whole
standard library still type-checks and executes cleanly.

## 11. `--config <path>` always crashed instead of loading the given config

**Symptom:** The documented way to point LoF at a non-default config file
(`lof check <workspace> --config path/to/config.yml`, needed to switch to
the FOL type system for anything beyond the default `./config.yml`) always
crashed:
```
thread 'main' panicked at src/main.rs:146:44:
called `Result::unwrap()` on an `Err` value: Io(Os { code: 2, kind: NotFound, message: "No such file or directory" })
```

**Root cause:** `get_flag_value` (`language/src/cli.rs`) searched `args` for
the element equal to `flag` and returned *that element itself*
(`arg.to_string()`) instead of the argument following it:
```rust
for arg in args {
    if arg == flag {
        return Some(arg.to_string());  // returns "--config", not its value
    }
}
```
So `--config path/to/config.yml` resolved to the config path literally being
the four-character string `"--config"`, which of course doesn't exist as a
file, so `load_config` always failed and `main`'s `.unwrap()` on it always
panicked. This is also how I initially failed to get an FOL-mode repro
running in this bug hunt (`proofr check file.lof --config custom.yml`) until
switching to `./config.yml` directly.

**Fix:** Return the argument at the *next* index instead of the matched
element itself.

**Verification:** New unit test
`test_get_flag_value_returns_the_following_argument` (in
`language/src/cli.rs`), covering the normal case, a missing flag, and the
flag being the last argument with nothing after it (must return `None`,
not panic). All 176 tests in `cargo test` pass.

## 12. The `auto` statement was unparseable as ordinary top-level source

**Symptom:** `auto formula;` - the documented syntax for automatic theorem
proving via saturation, and the *only* way to invoke it - failed to parse
from a real source file, even though the exact same string parsed
successfully when fed directly to the statement parser in isolation:
```
axiom Even : Nat -> PROP;
...
auto Even(s(s(z)));
```
```
Error parsing file '...'. Unparsed remainder starting at: ;
```

**Root cause:** Top-level source is parsed node-by-node via `parse_node`
(`language/src/parser/api.rs`), which tries `parse_expression` *before*
`parse_statement`. `solve` and `hclause` - `auto`'s siblings as top-level
statement keywords - are both in `RESERVED_KEYWORDS`
(`language/src/parser/commons.rs`), which makes `parse_identifier` (and so
`parse_var`/`parse_expression`) refuse to match them as a plain variable
name, forcing `parse_node` to fall through to `parse_statement` and parse
them correctly. `auto` was missing from that list, so `parse_expression`
happily matched the bare word `auto` on its own as a valid (if meaningless)
variable-reference expression-statement; `many0` then moved on and parsed
`Even(s(s(z)))` as its own, separate expression statement right after,
leaving the `;` that was meant to close the `auto` statement as unparseable
leftover input. `apply` (a tactic keyword, parsed via a separate,
dedicated grammar path that isn't affected by this particular ordering) was
missing from the same list too, reserved here for consistency with its
sibling tactic keywords (`begin`/`intro`/`exact`/`qed`), all of which
already are.

**Fix:** Added `auto` and `apply` to `RESERVED_KEYWORDS`.

**Verification:** New parser unit test
`test_auto_is_reserved_as_a_top_level_statement_keyword` (in
`language/src/tests/parser/statements.rs`), driving the parser the same way
`parse_source_file` actually does (`many0` over `parse_node`) rather than
calling `parse_statement` directly - which is what the pre-existing
`test_auto` did, and precisely why it never caught this: it never exercised
`parse_node`'s expression-before-statement ordering that the real bug lived
in. Manually re-verified `auto` now proves a real saturation goal end to end
in FOL mode. All 177 tests in `cargo test` pass, and the whole standard
library still type-checks and executes cleanly.

**Related, unimplemented (not a regression, so not fixed here):** while
chasing an FOL repro for this bug, `hclause` (Horn clauses) turned out to be
parsed but never actually elaborated or type-checked for either type system
- any `hclause ...;` statement is unconditionally rejected with "... is not
supported in FOL", even though it's documented as a real, distinct
statement form. `HClause` exists only in the parser's AST
(`language/src/parser/api.rs`) with no corresponding elaboration anywhere
under `language/src/type_theory/`. This looks like a feature that was
planned and partially wired up (the parser and its tests) but never
actually connected to a type system, rather than something that broke -
worth flagging since it means every `hclause` example in
`docs/language/syntax.md` currently doesn't work, but implementing real
Horn-clause elaboration is a feature addition, not a small fix.
