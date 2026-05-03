namespace prop10
-- (P → ¬P) ∨ (¬P → P)
-- Either branch is provable on its own once you know the truth value of P,
-- because the antecedent ends up unused.
theorem prop10 : (P → ¬ P) ∨ (¬ P → P) := by
  cases Classical.em P with
  | inl hP  => exact Or.inr (fun _ => hP)
  | inr hnP => exact Or.inl (fun _ => hnP)
end prop10
 
