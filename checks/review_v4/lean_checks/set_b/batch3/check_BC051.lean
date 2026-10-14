import Mathlib
open Matrix

-- kimina_autof hypotheses are contradictory: a real 2x2 skew-symmetric matrix has det = (H 0 1)^2 ≥ 0.
example (H : Matrix (Fin 2) (Fin 2) ℝ)
    (hH : H.det = -1) (hH1 : ∀ i j, H i j = -(H j i)) : False := by
  have h00 : H 0 0 = 0 := by have := hH1 0 0; linarith
  have h11 : H 1 1 = 0 := by have := hH1 1 1; linarith
  have h10 : H 1 0 = -(H 0 1) := hH1 1 0
  rw [det_fin_two, h00, h11, h10] at hH
  nlinarith [sq_nonneg (H 0 1)]

-- goedel_prover: Set.range (fun H => H) is all matrices, so the conclusion is trivial
example (H : Matrix (Fin 2) (Fin 2) ℝ) :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) * H ∈ Set.range (fun H => H) ∧
    H * (1 : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.range (fun H => H) :=
  ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
