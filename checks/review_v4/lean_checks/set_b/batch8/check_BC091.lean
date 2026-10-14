import Mathlib

-- kimina_autof's statement is plain distributivity in ℤ (no mod-n reduction of results)
example (n : ℕ) [NeZero n] (a b c : ℤ) :
    (a % n) * ((b % n) + (c % n)) = (a % n) * (b % n) + (a % n) * (c % n) ∧
    ((b % n) + (c % n)) * (a % n) = (b % n) * (a % n) + (c % n) * (a % n) := by
  constructor <;> ring

-- type of the expression: ℤ, not ZMod n
example (n : ℕ) (a : ℤ) : True := by
  have : (a % (n : ℤ)) = Int.emod a n := rfl
  trivial

-- a faithful version, also by ring
example (n : ℕ) (hn : 1 < n) (a b c : ℤ) :
    (a : ZMod n) * ((b : ZMod n) + (c : ZMod n)) = (a : ZMod n) * b + (a : ZMod n) * c ∧
    ((b : ZMod n) + c) * a = (b : ZMod n) * a + (c : ZMod n) * a := by
  constructor <;> ring
