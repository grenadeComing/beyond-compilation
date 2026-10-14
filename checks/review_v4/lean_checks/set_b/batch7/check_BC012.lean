import Mathlib

set_option pp.coercions true
set_option pp.explicit false

theorem gpt52_v (n : ℕ) :
    (ZMod n)ˣ = {u : ZMod n | Nat.gcd u.val n = 1} := by
  sorry
#check @gpt52_v
#print gpt52_v

theorem stepfun_v {n : ℕ} (hn : n ≠ 0) :
    ∀ a, IsUnit (a % n) ↔ Nat.gcd a n = 1 := by
  sorry
#check @stepfun_v

-- stepfun statement is false at n = 5, a = 2
example : ¬ (∀ {n : ℕ} (hn : n ≠ 0), ∀ a, IsUnit (a % n) ↔ Nat.gcd a n = 1) := by
  intro h
  have := (@h 5 (by norm_num) 2).2 (by norm_num)
  simp [Nat.isUnit_iff] at this

theorem kp_v : { a : ℤ | IsUnit (a : ZMod n) } = { a : ℤ | Int.gcd a n = 1 } := by sorry
#check @kp_v

-- kimina_prover statement is provable for all n (including n = 0)
example (n : ℕ) : { a : ℤ | IsUnit (a : ZMod n) } = { a : ℤ | Int.gcd a n = 1 } := by
  ext a
  simp only [Set.mem_setOf_eq]
  have hg : Int.gcd a (n : ℤ) = Nat.gcd a.natAbs n := by
    simp [Int.gcd, Int.natAbs_natCast]
  rw [hg, ← Nat.Coprime, ← ZMod.isUnit_iff_coprime]
  rcases Int.natAbs_eq a with h | h
  · conv_lhs => rw [h, Int.cast_natCast]
  · conv_lhs => rw [h, Int.cast_neg, Int.cast_natCast, IsUnit.neg_iff]
