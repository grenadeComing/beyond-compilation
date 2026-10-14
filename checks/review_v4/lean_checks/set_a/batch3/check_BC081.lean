import Mathlib

-- The norm on `Fin 2 → ℝ` is the sup norm (so `Isometry` refers to the sup metric):
example : ‖(fun _ : Fin 2 => (1 : ℝ))‖ = 1 := by simp [pi_norm_const]

-- The agent's statement is false at θ = 2π (second conjunct, x = (1,0)).
example : ¬ (let θ : ℝ := 2 * Real.pi
    let Rθ : Matrix (Fin 2) (Fin 2) ℝ :=
      !![Real.cos θ, -Real.sin θ;
        Real.sin θ,  Real.cos θ]
    let ρθ : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := (Matrix.toLin' Rθ)
    Isometry ρθ ∧
      ∀ x : Fin 2 → ℝ,
        x ≠ 0 →
          Complex.arg (Complex.ofReal (x 0) + Complex.I * Complex.ofReal (x 1)) + θ =
            Complex.arg
              (Complex.ofReal ((ρθ x) 0) + Complex.I * Complex.ofReal ((ρθ x) 1))) := by
  intro h
  obtain ⟨-, h2⟩ := h
  have hx : (![1, 0] : Fin 2 → ℝ) ≠ 0 := by
    intro h; have := congrFun h 0; simp at this
  have := h2 ![1, 0] hx
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
