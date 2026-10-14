import Mathlib

#print Matrix.specialOrthogonalGroup
-- The agent's BC044 statement is a definitional unfolding.
example (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] :
    (Matrix.specialOrthogonalGroup n R : Set (Matrix n n R)) =
      {A | A ∈ (Matrix.orthogonalGroup n R : Set (Matrix n n R)) ∧ Matrix.det A = 1} := by
  ext A; simp [Matrix.mem_specialOrthogonalGroup_iff]
