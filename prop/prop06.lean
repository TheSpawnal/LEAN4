namespace prop06
-- A ∨ B ↔ B ∨ A   :   commutativity of disjunction, fully constructive.
theorem prop06 : A ∨ B ↔ B ∨ A := by
  constructor
  · intro h
    cases h with
    | inl hA => exact Or.inr hA
    | inr hB => exact Or.inl hB
  · intro h
    cases h with
    | inl hB => exact Or.inr hB
    | inr hA => exact Or.inl hA
end prop06
