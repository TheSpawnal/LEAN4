namespace pred06

variable {P Q : Prop → Prop}

-- h  : ∃ x, Q x
--goal: ¬ ∀ x, P x ∧ ¬ ∃ y, P y
--Strategy: assume hall, pick any x; hall x gives (P x) and (¬ ∃ y, P y).
--however P x implies ∃ y, P y — contradiction.
theorem pred06 (h : ∃ x, Q x) : ¬ ∀ x, P x ∧ ¬ ∃ y, P y := by
  obtain ⟨w, _⟩ := h
  intro hall
  obtain ⟨hPw, hnex⟩ := hall w
  exact hnex ⟨w, hPw⟩

end pred06
