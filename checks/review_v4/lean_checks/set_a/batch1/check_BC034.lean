import Mathlib

#check @ZMod.isCyclic_units_iff

-- n = 0: ZMod 0 = ℤ, its unit group is cyclic, but the agent's RHS is false at n = 0.
example : IsCyclic ((ZMod 0)ˣ) := by
  rw [ZMod.isCyclic_units_iff]
  simp

example : ¬ (0 = 2 ∨ 0 = 4 ∨
        (∃ (p t : ℕ), Nat.Prime p ∧ p ≠ 2 ∧ 0 = p ^ t) ∨
        (∃ (p t : ℕ), Nat.Prime p ∧ p ≠ 2 ∧ 0 = 2 * p ^ t)) := by
  rintro (h | h | ⟨p, t, hp, -, h⟩ | ⟨p, t, hp, -, h⟩)
  · omega
  · omega
  · exact absurd h.symm (pow_ne_zero t hp.ne_zero)
  · exact absurd h.symm (mul_ne_zero two_ne_zero (pow_ne_zero t hp.ne_zero))
