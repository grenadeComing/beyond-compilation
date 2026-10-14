import Mathlib

-- For finite groups Sylow p G is nonempty, so `Subsingleton (Sylow p G)` ↔ exactly one Sylow p-subgroup.
example {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] : Nonempty (Sylow p G) := inferInstance

-- Logical equivalence of the agent's form with the "exactly one" form (no Sylow theory needed).
example {G : Type*} [Group G] {p : ℕ} :
    (Subsingleton (Sylow p G) → ∀ P : Sylow p G, (P.toSubgroup).Normal) ↔
    (∀ P : Sylow p G, (∀ Q : Sylow p G, Q = P) → (P.toSubgroup).Normal) := by
  constructor
  · intro h P hP
    exact h ⟨fun a b => (hP a).trans (hP b).symm⟩ P
  · intro h hs P
    exact h P (fun Q => Subsingleton.elim Q P)
