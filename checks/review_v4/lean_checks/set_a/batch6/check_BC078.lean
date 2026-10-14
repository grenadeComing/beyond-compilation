import Mathlib

open scoped Matrix

-- The identity r(θ) h r(θ) = h holds for EVERY θ, so `∃ θ` is trivial (θ = 0 works)
-- and carries no information about 2π/n.
theorem all_theta (θ : ℝ) :
    let r : Matrix (Fin 2) (Fin 2) ℝ := ![![Real.cos θ, -Real.sin θ], ![Real.sin θ, Real.cos θ]]
    let h : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0], ![0, -1]]
    r * h * r = h := by
  intro r h
  have hc := Real.cos_sq_add_sin_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [r, h, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [hc]

example {n : ℕ} (hn : 3 ≤ n) :
    ∃ θ : Real,
      (let r : Matrix (Fin 2) (Fin 2) Real :=
          ![![Real.cos θ, -Real.sin θ], ![Real.sin θ, Real.cos θ]]
        let h : Matrix (Fin 2) (Fin 2) Real := ![![1, 0], ![0, -1]]
        r * h * r = h) := ⟨0, all_theta 0⟩
