import Mathlib

-- Mathlib's matrix inverse is the adjugate-based one with junk value 0 on singular matrices
#print Matrix.inv
example : ((0 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ = 0 := Matrix.inv_zero

-- The stepfun statement is false: G = {0} is a counterexample at n = 1.
example : ¬ (∀ {n : ℕ} (hn : 0 < n) (G : Set (Matrix (Fin n) (Fin n) ℝ))
    (hG : G ≠ ∅) (hmul : ∀ A ∈ G, ∀ B ∈ G, A * B ∈ G) (hinv : ∀ A ∈ G, A⁻¹ ∈ G),
    1 ∈ G) := by
  intro h
  have := @h 1 one_pos {0} (Set.singleton_ne_empty _)
    (by intro A hA B hB; simp at hA hB; simp [hA, hB])
    (by intro A hA; simp at hA; simp [hA])
  simp at this
