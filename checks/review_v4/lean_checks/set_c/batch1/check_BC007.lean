import Mathlib

-- Int.ModEq is definitionally a % n = b % n
example (n a b : ℤ) : Int.ModEq n a b ↔ a % n = b % n := Iff.rfl

-- the Goedel statement (no positivity) holds for every integer n
theorem goedel_stmt {n a b c d : ℤ} (h₁ : a % n = b % n) (h₂ : c % n = d % n) :
    (a + c) % n = (b + d) % n := Int.ModEq.add h₁ h₂

-- remainder equality agrees with divisibility for all n (incl. n ≤ 0)
example (n a b : ℤ) : a % n = b % n ↔ n ∣ b - a := Int.modEq_iff_dvd

-- faithful version follows by specialization
example {n a b c d : ℤ} (hn : 0 < n) (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := goedel_stmt h₁ h₂

-- the Lean statement with n=0 is just equality
example (a b : ℤ) : a % 0 = b % 0 ↔ a = b := by simp
