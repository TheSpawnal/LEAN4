namespace prop05
-- ¬¬A ↔ A
-- Forward needs classical (byContradiction). Backward is constructive.
theorem prop05 : ¬¬ A ↔ A := by
  constructor
  · intro hnnA
    apply Classical.byContradiction
    intro hnA          -- hnA : ¬A ; goal : False
    exact hnnA hnA
  · intro hA hnA       -- ¬¬A unfolds to (A→False)→False ; here ¬A is the inner arg
    exact hnA hA
end prop05
