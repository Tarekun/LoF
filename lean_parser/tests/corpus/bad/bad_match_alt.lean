-- EXPECT: 7:2
def bad (n m : Nat) : Nat :=
  match n with
  | z => m
  | s nn =>
  match m with
  | z => n
  | s mm => bad nn mm
