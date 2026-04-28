namespace pred10

variable {P : Prop → Prop → Prop}

-- Goal: ∀ x, ∃ y, ∀ z, P x y ∨ ¬ P z y
-- h : ∀ x, (∃ y, P x y) ∨ (∀ y, ¬ P y x)
--
-- Fix x.  Case on h x:
--
-- Left  (∃ y, P x y):  get witness y with P x y.
--   For any z, P x y holds → left disjunct: P x y ∨ ¬ P z y. Done.
--
-- Right (∀ y, ¬ P y x): use y := x.
--   For any z, ¬ P z x holds (by applying right branch at z).
--   So right disjunct: P x x ∨ ¬ P z x  →  ¬ P z x witnesses it. Done.
theorem pred10 (h : ∀ x, (∃ y, P x y) ∨ (∀ y, ¬ P y x)) : ∀ x, ∃ y, ∀ z, P x y ∨ ¬ P z y := by
  intro x
  rcases h x with ⟨y, hPxy⟩ | hneg
  · exact ⟨y, fun _ => Or.inl hPxy⟩
  · exact ⟨x, fun z => Or.inr (hneg z)⟩

end pred10
