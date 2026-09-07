-- A nested `match` whose own alternatives are indented past the
-- enclosing match's alternatives -- the one case this design accepts.
def nested_match_ok (n m : Nat) : Nat :=
  match n with
  | z => m
  | s nn =>
    match m with
    | z => n
    | s mm => nested_match_ok nn mm
