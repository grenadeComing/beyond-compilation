import Mathlib

/-- The agent's statement (which faithfully renders the NL item) is false already for `n = 6`:
`N = ⊥` is a proper normal subgroup of `A_6`, but the stabilizer of `0` contains a 3-cycle. -/
theorem BC021_agent_false :
    ¬ (∀ (N : Subgroup (alternatingGroup (Fin 6))), N ≠ ⊤ → N.Normal →
      ∀ i : Fin 6, {σ : alternatingGroup (Fin 6) | (σ : Equiv.Perm (Fin 6)) i = i} ≤ N) := by
  intro h
  have h1 : (Equiv.swap (1 : Fin 6) 2 * Equiv.swap 2 3) ≠ 1 := by decide
  have hτ : (Equiv.swap (1 : Fin 6) 2 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have hne : (⊥ : Subgroup (alternatingGroup (Fin 6))) ≠ ⊤ := by
    intro hb
    have hm : (⟨_, hτ⟩ : alternatingGroup (Fin 6)) ∈ (⊥ : Subgroup (alternatingGroup (Fin 6))) := by
      rw [hb]; exact Subgroup.mem_top _
    rw [Subgroup.mem_bot] at hm
    exact h1 (congrArg Subtype.val hm)
  have hmem : (⟨_, hτ⟩ : alternatingGroup (Fin 6)) ∈
      {σ : alternatingGroup (Fin 6) | (σ : Equiv.Perm (Fin 6)) 0 = 0} := by
    simp only [Set.mem_setOf_eq]; decide
  have hb := h ⊥ hne inferInstance 0 hmem
  rw [SetLike.mem_coe, Subgroup.mem_bot] at hb
  exact h1 (congrArg Subtype.val hb)

#print axioms BC021_agent_false
