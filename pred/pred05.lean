namespace pred05

variable {P : Prop → Prop}

theorem pred05 : (∀ x, P x) → ¬ ∃ x, ¬ P x := by
  intro h ⟨x, hnx⟩
  exact hnx (h x)

end pred05
