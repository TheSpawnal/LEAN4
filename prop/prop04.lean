namespace prop04
-- Do not use Classical.byContradiction
-- This is not automatically checked so be extra careful here
-- You can (and probably want to) use Classical.em


-- (¬A → False) → A   without Classical.byContradiction
-- Use LEM to split on A directly.
theorem prop04 : (¬ A → False) → A := by
  intro h
  cases Classical.em A with
  | inl hA  => exact hA
  | inr hnA => exact False.elim (h hnA)
end prop04
