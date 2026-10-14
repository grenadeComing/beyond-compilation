import Mathlib

-- (ZMod 0)ˣ = ℤˣ = {±1} is cyclic, so Gemini's statement is false at n = 0.
example : IsCyclic (ZMod 0)ˣ := by
  show IsCyclic ℤˣ
  infer_instance

-- RHS of Gemini's statement at n = 0 is false.
example : ¬ ((0:ℕ) = 1 ∨ (0:ℕ) = 2 ∨ (0:ℕ) = 4 ∨
      (∃ p t : ℕ, p.Prime ∧ Odd p ∧ t ≠ 0 ∧ (0:ℕ) = p ^ t) ∨
      (∃ p t : ℕ, p.Prime ∧ Odd p ∧ t ≠ 0 ∧ (0:ℕ) = 2 * p ^ t)) := by
  rintro (h | h | h | ⟨p, t, hp, -, -, h⟩ | ⟨p, t, hp, -, -, h⟩)
  · omega
  · omega
  · omega
  · exact absurd h.symm (pow_ne_zero _ hp.ne_zero)
  · have := pow_ne_zero t hp.ne_zero; omega

-- Kimina-Autoformalizer's RHS: parse check, and n = 8 satisfies it (via p = 4, t = 1).
example : (8:ℕ) = 2 ∨ (8:ℕ) = 4 ∨ ∃ p t, Odd p ∧ Nat.Prime p ∧ (8:ℕ) = p ^ t ∨ (8:ℕ) = 2 * p ^ t := by
  right; right; exact ⟨4, 1, Or.inr rfl⟩

-- (ZMod 8)ˣ is not cyclic
example : ¬ IsCyclic (ZMod 8)ˣ := by
  intro h
  have hsq : ∀ g : (ZMod 8)ˣ, g ^ 2 = 1 := by decide
  have he : Monoid.exponent (ZMod 8)ˣ ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hsq
  rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at he
  revert he; decide

-- Herald: check the autobound signature
theorem exists_primitive_root_iff_ext {n : ℕ} :
    (∃ g : (ZMod n)ˣ, IsPrimitiveRoot g n) ↔
      n = 2 ∨ n = 4 ∨ (∃ p : ℕ, p.Prime ∧ n = p ^ t ∨ n = 2 * p ^ t) := sorry
#check @exists_primitive_root_iff_ext
