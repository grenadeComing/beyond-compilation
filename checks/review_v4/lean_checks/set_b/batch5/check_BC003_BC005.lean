import Mathlib

universe u

-- In `[AddCommGroup R] [CommSemiring R]` the two structures are independent:
-- `-` comes from the AddCommGroup, `*` (and `1`) from the CommSemiring.
-- Counterexample: ℤ with its usual CommSemiring, and the AddCommGroup transported
-- along x ↦ x + 1 (so the group's zero is -1 and its negation is a ↦ -a - 2).

-- kimina_prover, BC003
example : ¬ ∀ (R : Type) [AddCommGroup R] [CommSemiring R] (a b : R),
    (-a) * (-b) = a * b := by
  intro h
  have := @h ℤ ((Equiv.addRight (1 : ℤ)).addCommGroup) inferInstance 0 0
  simp [Equiv.neg_def] at this

-- kimina_prover, BC005
example : ¬ ∀ (R : Type) [AddCommGroup R] [CommSemiring R] (a : R),
    (-1 : R) * a = -a := by
  intro h
  have := @h ℤ ((Equiv.addRight (1 : ℤ)).addCommGroup) inferInstance 0
  simp [Equiv.neg_def] at this
