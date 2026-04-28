namespace pred02

variable {P Q : Prop → Prop}

theorem pred02 (h : ∀ x, Q x) : (∃ x, Q x → P x) → ∃ x, P x := by
  intro ⟨x, hx⟩
  exact ⟨x, hx (h x)⟩

end pred02
