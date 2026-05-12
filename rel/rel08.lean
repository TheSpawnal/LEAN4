namespace rel08

variable {a : Prop} {R : Prop → Prop → Prop}

theorem rel08 : (∀ x, R x a) → ¬ R a a → ∀ x, R x x := by
  sorry

end rel08
