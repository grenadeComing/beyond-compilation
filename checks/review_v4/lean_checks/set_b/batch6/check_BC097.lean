import Mathlib

-- The kimina_prover encoding `a % n = b % n` (n : ℕ cast to ℤ) is definitionally Mathlib's Int.ModEq
example (n : ℕ) (a b : ℤ) : (a % n = b % n) ↔ a ≡ b [ZMOD n] := Iff.rfl
-- and is equivalent to Doty's definition n ∣ (a - b), for every n including 0
example (n : ℕ) (a b : ℤ) : (a % n = b % n) ↔ (n : ℤ) ∣ (a - b) := by
  rw [show (a % n = b % n) ↔ a ≡ b [ZMOD n] from Iff.rfl, Int.modEq_comm, Int.modEq_iff_dvd]
set_option pp.coercions true in
example (n : ℕ) (a b : ℤ) : True := by
  have h : (a % n = b % n) = (a % (n : ℤ) = b % (n : ℤ)) := rfl
  trivial
