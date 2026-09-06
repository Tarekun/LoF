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
