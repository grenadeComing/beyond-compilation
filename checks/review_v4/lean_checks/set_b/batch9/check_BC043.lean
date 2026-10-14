import Mathlib

-- goedel_prover statement: conclusion is a direct rewrite of the hypothesis
theorem srdoty_alg_linear_gps_380 (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.transpose * A = 1) :
    ∀ (i j : Fin n), i ≠ j → (A.transpose * A) i j = 0 := by
  intro i j hij
  rw [hA, Matrix.one_apply_ne hij]
