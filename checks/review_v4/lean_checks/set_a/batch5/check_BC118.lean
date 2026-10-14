import Mathlib

open MeasureTheory

-- The measurable space on Fin n → ℝ is the Borel σ-algebra
example (n : ℕ) : BorelSpace (Fin n → ℝ) := inferInstance
example (n : ℕ) : (inferInstance : MeasurableSpace (Fin n → ℝ)) = borel (Fin n → ℝ) :=
  BorelSpace.measurable_eq

-- Mathlib has the boundary-null-set fact needed for a faithful Jordan-measurability statement
#check @Convex.addHaar_frontier
#check @Convex.nullMeasurableSet

example (n : ℕ) (s : Set (Fin n → ℝ)) (hb : Bornology.IsBounded s) (hc : Convex ℝ s) :
    Bornology.IsBounded s ∧ volume (frontier s) = 0 :=
  ⟨hb, hc.addHaar_frontier volume⟩
