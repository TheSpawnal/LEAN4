namespace pred04

variable {P : Prop → Prop}

theorem pred04 : (∀ x, ¬ P x) → ¬ ∃ x, P x := by
  intro h ⟨x, hx⟩
  exact h x hx

end pred04
