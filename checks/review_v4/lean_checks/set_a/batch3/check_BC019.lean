import Mathlib

-- No group is MulEquiv to the multiplicative monoid of a nontrivial `ZMod m`.
theorem no_mulEquiv_zmod {G : Type*} [Group G] (m : ℕ) [Nontrivial (ZMod m)]
    (e : G ≃* ZMod m) : False := by
  have key : ∀ h : G, h = 1 := by
    intro h
    have : e.symm 0 * h = e.symm 0 := by
      apply e.injective
      rw [map_mul, MulEquiv.apply_symm_apply, zero_mul]
    simpa using this
  have h0 : (0 : ZMod m) = 1 := by
    have := congrArg e (key (e.symm 0))
    simpa using this
  exact zero_ne_one h0

-- Dihedral group convention: |DihedralGroup n| = 2n
example (n : ℕ) [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n := DihedralGroup.card

-- The agent's BC019 conclusion fails for G = Multiplicative (ZMod 6), p = 3.
example : ¬ (Nonempty (Multiplicative (ZMod 6) ≃* ZMod (2*3)) ∨
    Nonempty (Multiplicative (ZMod 6) ≃* DihedralGroup 3)) := by
  rintro (h | h)
  · obtain ⟨e⟩ := h
    haveI : Fact (1 < 2*3) := ⟨by norm_num⟩
    exact no_mulEquiv_zmod (2*3) e
  · obtain ⟨e⟩ := h
    have hc : ∀ a b : DihedralGroup 3, a * b = b * a := by
      intro a b
      apply e.symm.injective
      rw [map_mul, map_mul, mul_comm]
    have := hc (DihedralGroup.r 1) (DihedralGroup.sr 0)
    revert this; decide

-- BC024: a simple quotient of order p exists (G = Multiplicative (ZMod p), H = ⊤, K = ⊥)
-- but the conclusion `≃* ZMod p` is impossible for any group.
example (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q] : IsEmpty (Q ≃* ZMod p) :=
  ⟨fun e => no_mulEquiv_zmod p e⟩
