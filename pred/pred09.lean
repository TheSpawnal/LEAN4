namespace pred09

variable {P Q R: Prop → Prop}

theorem pred09 (h : ∀ x, (R x → P x)) : (∀ x, Q x ∧ R x) → ∀ x, P x ∧ Q x := by
  intro hall x
  obtain ⟨hQx, hRx⟩ := hall x
  exact ⟨h x hRx, hQx⟩

end pred09
