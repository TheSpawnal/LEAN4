namespace prop01
-- A ∧ (A → B) → B   :   modus ponens hidden behind a conjunction
theorem prop01 : A ∧ (A → B) → B := by
  intro ⟨hA, hAB⟩
  exact hAB hA
end prop01
