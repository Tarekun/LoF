def let_semicolon := let x := 1; x

def let_newline :=
  let x := 1
  x

def have_form :=
  have h := 1
  h

def nested_let :=
  let a := 1
  let b := 2
  a + b

def let_with_type :=
  let x : Nat := 1
  x
