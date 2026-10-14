import Mathlib

-- The agent's BC041 statement is closed by the pre-existing instance (no content about AAᵀ = I).
example (n : ℕ) : Nonempty (Group (Matrix.orthogonalGroup (Fin n) ℝ)) := ⟨inferInstance⟩

-- `Nonempty (Group α)` is insensitive to matrix multiplication: any type in bijection
-- with a group carries a group structure.
example : Nonempty (Group (Fin 7)) := ⟨Equiv.group (β := Multiplicative (ZMod 7)) (Equiv.refl _)⟩

#print Matrix.orthogonalGroup
#check @Matrix.mem_orthogonalGroup_iff
