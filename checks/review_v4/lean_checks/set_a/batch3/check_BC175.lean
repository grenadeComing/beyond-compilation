import Mathlib

#check @OnePoint
#check @OnePoint.isOpen_iff_of_mem
#check @onePointEquivSphereOfFinrankEq

-- The agent's target type is inhabited via Mathlib's stereographic-projection homeomorphism.
noncomputable example (n : ℕ) :
    OnePoint (EuclideanSpace ℝ (Fin n)) ≃ₜ
      {x : EuclideanSpace ℝ (Fin (n + 1)) // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1} :=
  onePointEquivSphereOfFinrankEq (by simp)
