namespace prop03
-- Do not use Classical.em
-- This is not automatically checked so be extra careful here
-- You can (and probably want to) use Classical.byContradiction

-- A ∨ ¬A   without Classical.em
-- Trick: assume the negation, build BOTH disjuncts to feed the contradiction.
theorem prop03 : A ∨ ¬A := by
  apply Classical.byContradiction
  intro h            -- h : ¬(A ∨ ¬A) ; goal : False
  apply h            -- goal becomes A ∨ ¬A
  apply Or.inr       -- pick the ¬A side ; goal becomes ¬A
  intro hA           -- hA : A ; goal : False
  apply h            -- goal becomes A ∨ ¬A again
  apply Or.inl
  exact hA
end prop03
