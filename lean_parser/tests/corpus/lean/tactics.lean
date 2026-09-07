theorem modeled_tactics : P := by
  intro n
  apply foo
  exact bar

theorem seq_focus_tactic : P := by
  intro n <;> exact bar

theorem unknown_tactics_are_captured : P := by
  simp
  rfl

theorem unknown_tactic_with_brackets : P := by
  simp [foo, bar]

theorem constructor_tactic : P := by
  constructor
