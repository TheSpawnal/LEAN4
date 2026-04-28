namespace pred07

variable {Person : Type}
variable {shaves : Person → Person → Prop}
variable {barber : Person}

theorem pred07 : ¬ ∀ (x : Person), shaves barber x ↔ ¬ shaves x x := by
  intro h
  -- h is: ∀ x, shaves barber x ↔ ¬ shaves x x
  --I specialize it to the barber themselves:
  have h_barber := h barber
  --now h_barber is: shaves barber barber ↔ ¬ shaves barber barber
  --this is a classic contradiction (A ↔ ¬A)
  by_cases h_shaves : shaves barber barber
  · -- Case 1: The barber shaves himself
    have h_not_shaves := h_barber.mp h_shaves
    exact h_not_shaves h_shaves
  · -- Case 2: The barber does not shave himself
    have h_shaves_again := h_barber.mpr h_shaves
    exact h_shaves h_shaves_again

end pred07


-- namespace pred07

-- variable {Person : Type}
-- variable {shaves : Person → Person → Prop}
-- variable {barber : Person}

-- -- h    : ∀ x, shaves barber x ↔ ¬ shaves x x
-- -- goal : False (after intro)
-- -- Strategy: specialise the universal at the barber. The result is
-- -- A ↔ ¬A, the canonical self-referential contradiction. From the
-- -- forward direction we constructively obtain ¬A (assume A, derive
-- -- ¬A, apply it to A). Feeding that ¬A into the backward direction
-- -- recovers A, which we then refute with our ¬A.
-- theorem pred07 : ¬ ∀ (x : Person), shaves barber x ↔ ¬ shaves x x := by
--   intro h
--   obtain ⟨mp, mpr⟩ := h barber
--   have hn : ¬ shaves barber barber := fun hs => mp hs hs
--   exact hn (mpr hn)

-- end pred07
