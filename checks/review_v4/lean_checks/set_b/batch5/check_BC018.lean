import Mathlib

-- herald: hypothesis `∀ x, IsPrimePow (orderOf x)` is unsatisfiable (orderOf 1 = 1, not a prime power),
-- so the statement is vacuously provable.
theorem herald_BC018_vacuous {α : Type*} [Group α] {p : ℕ} [hp : Fact (Nat.Prime p)] :
    (∀ (x : α), IsPrimePow (orderOf x)) → ∀ [Fintype α], ∃ r, Fintype.card α = p ^ r := by
  intro h
  exact absurd (h 1) (by simp [not_isPrimePow_one])

-- kimina_autof: false already for the trivial group (r ≥ 1 forced), via the prime varying per element.
example : ¬ (∀ {G : Type} [Group G] [Fintype G],
    (∀ g : G, ∃ (p k : ℕ), Nat.Prime p ∧ p ^ k = orderOf g) →
    ∃ (p r : ℕ), Nat.Prime p ∧ Fintype.card G = p ^ r ∧ r ≥ 1) := by
  intro h
  obtain ⟨p, r, hp, hc, hr⟩ := @h Unit _ _ (fun g => ⟨2, 0, Nat.prime_two, by rw [pow_zero, eq_comm, orderOf_eq_one_iff]⟩)
  have : 1 < p ^ r := Nat.one_lt_pow (by omega) hp.one_lt
  simp at hc
  omega

-- gpt52 output's conclusion with r ≥ 1 would be false for the trivial group (NL defect):
example (p : ℕ) [Fact p.Prime] : ¬ ∃ r : ℕ, r ≥ 1 ∧ Fintype.card Unit = p ^ r := by
  rintro ⟨r, hr, hc⟩
  have : 1 < p ^ r := Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
  simp at hc
  omega
