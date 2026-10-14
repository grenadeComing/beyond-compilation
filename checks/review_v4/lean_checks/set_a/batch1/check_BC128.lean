import Mathlib

-- Counterexample to the agent's statement: n = 2, a = (1,1), b = (0,0).
-- Icc a b = ∅ so the outer measure is 0, but ofReal ((0-1)*(0-1)) = 1.
example : ¬ ((MeasureTheory.volume.toOuterMeasure (Set.Icc (fun _ : Fin 2 => (1:ℝ)) (fun _ => 0)))
    = ENNReal.ofReal (∏ i : Fin 2, ((fun _ : Fin 2 => (0:ℝ)) i - (fun _ : Fin 2 => (1:ℝ)) i))) := by
  have hE : Set.Icc (fun _ : Fin 2 => (1:ℝ)) (fun _ => 0) = ∅ := by
    apply Set.Icc_eq_empty
    intro h
    have := h 0
    norm_num at this
  rw [hE]
  simp [Fin.prod_univ_two]

#check @Real.volume_Icc_pi
