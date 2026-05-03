namespace prop07
-- (¬A ∨ ¬B) → ¬(A ∧ B)
-- Goal ¬(A∧B) = (A∧B)→False, so intro and destructure ; then case-split the OR.
theorem prop07 : (¬ A ∨ ¬ B) → ¬ (A ∧ B) := by
  intro hOr ⟨hA, hB⟩
  cases hOr with
  | inl hnA => exact hnA hA
  | inr hnB => exact hnB hB
end prop07
