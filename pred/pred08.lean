namespace pred08

variable {P : Prop} {Q R : Prop → Prop}

-- Goal: ∃ x, P → Q x
-- We always have ∃ x, R x (h2).  Two cases on P:
--   Case P holds : use h1 to get ∃ x, Q x; wrap it as P → Q x.
--   Case ¬P holds: use the witness from h2; the implication P → Q w is
--                  vacuously true because the premise is false.
theorem pred08 (h1 : P → ∃ x, Q x) (h2 : ∃ x, R x) : ∃ x, P → Q x := by
  obtain ⟨w, _⟩ := h2
  by_cases hp : P
  · obtain ⟨x, hx⟩ := h1 hp
    exact ⟨x, fun _ => hx⟩
  · exact ⟨w, fun hp' => absurd hp' hp⟩

end pred08
