import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem srdoty_alg.AbstractGPS_1008 (O : Set (Matrix (Fin 2) (Fin 2) ℝ))
    (hO : O = {A : Matrix (Fin 2) (Fin 2) ℝ | A.det = 1 ∧ ∀ i j, i ≠ j → A i j * A j i = 0})
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A ∈ O \ {A : Matrix (Fin 2) (Fin 2) ℝ | ∃ θ, A = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]})
    : closure {A} = O := by sorry

set_option pp.fullNames true in
#print srdoty_alg.AbstractGPS_1008

-- goedel_prover's statement is trivial: R = A⁻¹ * B.
example : ∀ (A : Matrix (Fin 2) (Fin 2) ℝ), A.det = -1 → ∀ (B : Matrix (Fin 2) (Fin 2) ℝ), B.det = -1 →
    B ∈ Set.range (fun (R : Matrix (Fin 2) (Fin 2) ℝ) => A * R) := by
  intro A hA B _
  refine ⟨A⁻¹ * B, ?_⟩
  have : IsUnit A.det := by rw [hA]; exact isUnit_one.neg
  simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv A this]
