import Mathlib
open Matrix

-- kimina_autof's statement is false: with F = ℚ, A = B = E(0) = 1 ∈ G, but 1 ≠ !![x,1;0,x].
example : ¬ (∀ (F : Type) [Field F] (G : Set (Matrix (Fin 2) (Fin 2) F)) (hG : G = { !![1, t; 0, 1] | t : F }),
    ∀ A ∈ G, ∀ B ∈ G, A * B ∈ G ∧ (∃ x : F, A = !![x, 1; 0, x]) ∧ (∃ x : F, B = !![x, 1; 0, x])) := by
  intro h
  have hmem : (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) ∈ { !![1, t; 0, 1] | t : ℚ } := ⟨0, rfl⟩
  obtain ⟨_, ⟨x, hx⟩, _⟩ := h ℚ _ rfl _ hmem _ hmem
  have := congrFun (congrFun hx 0) 1
  simp at this
