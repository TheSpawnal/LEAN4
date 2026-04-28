namespace pred03

variable {P : Prop → Prop → Prop}

theorem pred03 (h : ∃ x, ∀ y, P y x) : ∀ x, ∃ y, P x y := by
  obtain ⟨a, ha⟩ := h
  intro x
  exact ⟨a, ha x⟩

end pred03
