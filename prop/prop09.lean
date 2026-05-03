namespace prop09
-- (A → B) → (A → ¬B) → ¬A
-- Two implications agreeing/disagreeing on A's image yield ¬A directly.
theorem prop09 : (A → B) → (A → ¬ B) → ¬ A := by
  intro hAB hAnB hA
  exact hAnB hA (hAB hA)
end prop09
 
