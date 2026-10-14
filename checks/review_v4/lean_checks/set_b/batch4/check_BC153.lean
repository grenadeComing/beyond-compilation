import Mathlib

-- For n = 1 the whole space has infinite volume, so its toReal is 0:
-- the kimina_autof hypothesis is satisfied by Y = univ for every X.
example : (MeasureTheory.volume (Set.univ : Set (EuclideanSpace ℝ (Fin 1)))).toReal = 0 := by
  rw [MeasureTheory.measure_univ_of_isAddLeftInvariant]
  simp

#check @ENNReal.toReal_top
