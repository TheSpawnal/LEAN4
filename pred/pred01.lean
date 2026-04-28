namespace pred01

variable {R : Prop -> Prop -> Prop}

theorem pred01 : (∀ x, ∀ y, R x y) → ∀ x, R x x := by
  intro h x
  exact h x x

end pred01
