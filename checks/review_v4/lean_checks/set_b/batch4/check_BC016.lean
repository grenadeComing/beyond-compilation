import Mathlib

theorem stepfun_srdoty_alg_Sylow_625 : ∀ n : ℕ, 0 < n → {C | ∃ π, C = {σ | σ ^ π = π}}.ncard = {p : Finset ℕ | p.sum id = n}.ncard := by
  sorry

set_option pp.all false in
#check @stepfun_srdoty_alg_Sylow_625
set_option pp.funBinderTypes true in
#print stepfun_srdoty_alg_Sylow_625

-- kimina_autof: LHS counts all permutations (n!), RHS is n
example : (Nat.card (Finset.univ : Finset (Fin 3))) = 3 := by simp
example : {p : Equiv.Perm (Fin 3) | ∃ c : Fin 3 → Fin 3, p = c}.ncard = 6 := by
  have : {p : Equiv.Perm (Fin 3) | ∃ c : Fin 3 → Fin 3, p = c} = Set.univ := by
    ext p; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact ⟨p, rfl⟩
  rw [this, Set.ncard_univ, Nat.card_perm]; simp [Nat.card_eq_fintype_card]; decide
