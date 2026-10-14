import Mathlib

open Matrix

-- `Aᵀ *ᵥ e_i` is the i-th ROW of A, not the i-th column.
example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Aᵀ.mulVec (Pi.single i 1) = A i := by
  ext k; simp [Matrix.mulVec_single]

-- the i-th column is `A *ᵥ e_i`
example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    A.mulVec (Pi.single i 1) = fun k => A k i := by
  ext k; simp [Matrix.mulVec_single]

-- Mathlib's orthogonal group membership gives both AᵀA = 1 and AAᵀ = 1
example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A ∈ Matrix.orthogonalGroup (Fin n) ℝ ↔ star A * A = 1 ∧ A * star A = 1 := Iff.rfl

-- the agent's row statement follows directly from A * Aᵀ = 1
example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (i j : Fin n) :
    (Aᵀ.mulVec (Pi.single i 1)) ⬝ᵥ (Aᵀ.mulVec (Pi.single j 1)) = (if i = j then (1 : ℝ) else 0) := by
  have h := congrFun (congrFun hA.2 i) j
  simp [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.one_apply, dotProduct,
    Matrix.mulVec_single] at h ⊢
  rw [← h]
