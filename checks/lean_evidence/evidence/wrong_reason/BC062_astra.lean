/-! Judge claim: with Mathlib's convention `Equiv.swap 0 1 * Equiv.swap 1 2` is the 3-cycle
inverse to (0 1 2), i.e. (0 2 1). In Mathlib `(σ * τ) x = σ (τ x)`, so the product is (0 1 2). -/

/-- The output's `β` sends 0 ↦ 1, 1 ↦ 2, 2 ↦ 0 (the relabeling of (1 2 3)). -/
theorem claim_beta_values :
    let β : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
    β 0 = 1 ∧ β 1 = 2 ∧ β 2 = 0 := by decide

/-- The output's `β` equals the cycle c[0, 1, 2]. -/
theorem claim_beta_eq_cycle_012 :
    (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) = c[0, 1, 2] := by decide

/-- The output's `β` is NOT the cycle (0 2 1) that the judge names. -/
theorem claim_beta_ne_cycle_021 :
    (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) ≠ c[0, 2, 1] := by decide

/-- Extra: the output's statement itself is true (proved without sorry). -/
theorem claim_statement_true :
    let α : Equiv.Perm (Fin 3) := Equiv.swap 0 1
    let β : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
    Subgroup.closure ({α, β} : Set (Equiv.Perm (Fin 3))) = ⊤ := by
  intro α β
  have e : β = List.formPerm [0, 1, 2] := by decide
  have hβ : β.IsCycle := by
    rw [e]; exact List.isCycle_formPerm (by decide) (by decide)
  have hs : β.support = Finset.univ := by decide
  have h := Equiv.Perm.closure_cycle_adjacent_swap hβ hs 0
  have h1 : β 0 = 1 := by decide
  rw [h1] at h
  rw [Set.pair_comm]
  exact h
