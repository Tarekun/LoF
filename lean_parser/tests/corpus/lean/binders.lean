def explicit_binder (x y : Nat) : Nat := x

def implicit_binder {x : Nat} : Nat := x

def strict_implicit_binder ⦃x : Nat⦄ : Nat := x

def inst_implicit_binder [Foo] : Nat := zero

def mixed_binders (x : Nat) {y : Nat} [Inst] : Nat := x

-- a trailing bare-name run shares one type: both x and y are Nat
theorem shared_type_binder : forall x y : Nat, x = x := by
  intro x y
  exact rfl_marker

def fun_shared_type := fun x y : Nat => x

def dependent_arrow (n : Nat) : (m : Nat) -> Nat := fun m => m
