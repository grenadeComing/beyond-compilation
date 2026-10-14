import Mathlib

-- Mathlib's junk inverse: the zero matrix is its own "inverse".
example : (0 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = 0 := Matrix.inv_zero

-- The agent's statement (specialised to n = Fin 1) is false: G = {0} is a counterexample.
example : ¬ (∀ (G : Set (Matrix (Fin 1) (Fin 1) ℝ)), G.Nonempty →
    (∀ {A B}, A ∈ G → B ∈ G → A * B ∈ G) → (∀ {A}, A ∈ G → A⁻¹ ∈ G) →
      (1 : Matrix (Fin 1) (Fin 1) ℝ) ∈ G) := by
  intro h
  have := h {0} ⟨0, rfl⟩ (by intro A B hA hB; simp_all) (by intro A hA; simp_all)
  simp at this
