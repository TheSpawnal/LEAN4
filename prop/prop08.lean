namespace prop08
-- B → ¬(¬A ∧ ¬(B ∨ ¬C))
-- The hidden claim: knowing B alone refutes the inner conjunction,
-- because B builds (B ∨ ¬C), contradicting its negation. ¬A is unused.
theorem prop08 : B → ¬ (¬ A ∧ ¬ (B ∨ ¬ C)) := by
  intro hB ⟨_, hnBnC⟩
  exact hnBnC (Or.inl hB)
end prop08
