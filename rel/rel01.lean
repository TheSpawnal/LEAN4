namespace rel01

variable {a b : Prop} {R : Prop -> Prop -> Prop}

theorem rel01 (h1 : ∀ x, R a x → a = x) (h2 : ∀ x, R x b): a = b := by
  sorry

end rel01
