import Mathlib
open Equiv

-- herald statement is exactly a Mathlib lemma
example (n : ℕ) :
    Submonoid.closure (Set.range fun i : Fin n ↦ swap i.castSucc i.succ) = ⊤ :=
  Equiv.Perm.mclosure_swap_castSucc_succ n

-- ambient type is Perm (Fin (n+1))
example (n : ℕ) : (Set.range fun i : Fin n ↦ swap i.castSucc i.succ) ⊆ (Set.univ : Set (Perm (Fin (n+1)))) :=
  Set.subset_univ _

-- herald form implies the NL (subgroup-generation) form for S_m, m = n+1
example (n : ℕ) :
    Subgroup.closure (Set.range fun i : Fin n ↦ (swap i.castSucc i.succ : Perm (Fin (n+1)))) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : g ∈ Submonoid.closure (Set.range fun i : Fin n ↦ (swap i.castSucc i.succ : Perm (Fin (n+1)))) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ n]; trivial
  exact (Submonoid.closure_le (S := (Subgroup.closure _).toSubmonoid)).mpr Subgroup.subset_closure hg
