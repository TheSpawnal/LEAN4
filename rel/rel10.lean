namespace rel10

variable {a b : Prop} {R S : Prop → Prop → Prop}

theorem rel10 (h : ∀ x y, R x y → S y x) : (∃ x, R x a ∧ x = b) → S a b:= by
  sorry

end rel10
