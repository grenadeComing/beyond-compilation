import Mathlib

-- The kimina_prover statement, verbatim (proof sorry)
theorem srdoty_alg_Z_n_511 (R : Type u_1) [AddCommGroup R] [CommSemiring R] (a b c : R) :
    a * (b - c) = a * b - a * c := by sorry

set_option pp.explicit true in
#check @srdoty_alg_Z_n_511

-- Counterexample: R = ℤ, standard CommSemiring, but AddCommGroup transported along x ↦ x + 1.
-- Then the subtraction is unrelated to the semiring addition and the identity fails.
theorem BC004_statement_false :
    ¬ (∀ (R : Type) [AddCommGroup R] [CommSemiring R] (a b c : R), a * (b - c) = a * b - a * c) := by
  intro h
  have key := @h ℤ ((Equiv.addRight (1 : ℤ)).addCommGroup) Int.instCommSemiring 2 0 0
  simp [Equiv.sub_def] at key
