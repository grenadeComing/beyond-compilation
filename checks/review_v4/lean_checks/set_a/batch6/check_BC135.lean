import Mathlib

open MeasureTheory

-- The agent's conclusion holds for EVERY f (no boundedness, no measurability):
-- a degenerate box has volume 0, so Lebesgue integrability and integral 0 are automatic.
example {n : ℕ} {a b : Fin n → ℝ} (hside : ∃ i : Fin n, a i = b i)
    (f : (Fin n → ℝ) → ℝ) :
    IntegrableOn f (Set.Icc a b) ∧ (∫ x in Set.Icc a b, f x = (0 : ℝ)) := by
  obtain ⟨i, hi⟩ := hside
  have h0 : volume (Set.Icc a b) = 0 := by
    rw [Real.volume_Icc_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  refine ⟨?_, ?_⟩
  · have : (volume.restrict (Set.Icc a b)) = 0 := Measure.restrict_eq_zero.mpr h0
    simp [IntegrableOn, this]
  · exact setIntegral_measure_zero f h0
