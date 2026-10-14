import Mathlib

/-- The agent's statement, universally quantified, is false: take `R = ℕ` with the usual
`+` and `*` := `max`. Then `Nonempty (Ring ℕ)` holds (transport from `ℤ`), but the given
`+`/`*` do not distribute. -/
theorem BC026_agent_false :
    ¬ (∀ (R : Type) [Add R] [Mul R],
      (Nonempty (Ring R)) ↔
      (∃ (zero : R),
          (letI : Zero R := ⟨zero⟩
           Nonempty (AddCommGroup R)) ∧
        ∃ (one : R),
          (letI : One R := ⟨one⟩
           Nonempty (Monoid R)) ∧
        (∀ a b c : R, a * (b + c) = a * b + a * c) ∧
          (∀ a b c : R, (b + c) * a = b * a + c * a))) := by
  intro h
  have hR : Nonempty (Ring ℕ) := ⟨Equiv.intEquivNat.symm.ring⟩
  obtain ⟨_, _, _, _, hd, _⟩ := (@h ℕ ⟨Nat.add⟩ ⟨max⟩).mp hR
  have h3 := hd 1 0 0
  revert h3
  decide

#print axioms BC026_agent_false
