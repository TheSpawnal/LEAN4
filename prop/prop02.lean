namespace prop02
-- ((A → C) ∨ (B → C)) → A ∧ B → C
-- Disjunction in context => cases ; both branches close trivially.
theorem prop02 : ((A → C) ∨ (B → C)) → A ∧ B → C := by
  intro hOr ⟨hA, hB⟩
  cases hOr with
  | inl hAC => exact hAC hA
  | inr hBC => exact hBC hB
end prop02
