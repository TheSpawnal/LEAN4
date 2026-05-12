namespace rel04

variable {R : Prop → Prop → Prop}

theorem rel04 (irrefl : ∀ x, ¬ R x x)
              (trans : ∀ x y z, R x y → R y z → R x z) :
              ∀ x y, R x y → ¬ R y x := by
  sorry

end rel04
