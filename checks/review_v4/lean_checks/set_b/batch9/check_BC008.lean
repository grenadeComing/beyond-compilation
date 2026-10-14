import Mathlib

-- goedel_prover statement: proof is definitional
theorem srdoty_alg_Z_n_779 (n : ℕ) (a b : ℤ) : (a ≡ b [ZMOD n]) ↔ (a % n = b % n) := Iff.rfl

set_option pp.explicit true in
#check @srdoty_alg_Z_n_779

#print Int.ModEq

-- n = 0 case: both sides reduce to a = b, matching the divisibility definition 0 ∣ a - b
example (a b : ℤ) : (a ≡ b [ZMOD (0:ℕ)]) ↔ a = b := by simp [Int.ModEq]

-- remainder is the Euclidean (nonnegative) one for n > 0
example (a : ℤ) (n : ℕ) (hn : 0 < n) : 0 ≤ a % (n:ℤ) ∧ a % (n:ℤ) < n :=
  ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩

-- propositional equivalence with the textbook (Gauss) definition n ∣ a - b
example (n : ℕ) (a b : ℤ) : (a ≡ b [ZMOD n]) ↔ (n:ℤ) ∣ a - b := by
  rw [Int.modEq_comm, Int.modEq_iff_dvd]
