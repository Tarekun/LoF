-- A `by` block whose last tactic is directly followed by a col-0 `def`:
-- the term parser inside `exact` must not swallow the next declaration.
theorem indented_by_block : P := by
  intro n
  exact foo n

def after_by := 1

-- A `match` nested inside `by exact`.
theorem match_inside_by : P := by
  exact
    match n with
    | z => a
    | s nn => b

def let_chain :=
  let a := 1
  let b := 2
  a + b
