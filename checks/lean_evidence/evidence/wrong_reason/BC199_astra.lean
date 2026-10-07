/-! Judge claim: the conditions `(p.trans q) 1 = z 0` and `x 1 = (q.trans r) 0` (with z, resp. x,
not required to come from a `Path`) do not capture the endpoint compatibility for definedness.
In fact each side is equivalent to `x 1 = y 0 ∧ y 1 = z 0`, which is exactly
"(x*y)*z defined" (resp. "x*(y*z) defined"); every continuous map is a `Path` between its endpoints. -/

theorem claim_lhs_iff_endpoints {X : Type*} [TopologicalSpace X]
    (x y z : ContinuousMap (Set.Icc (0 : ℝ) 1) X) :
    (∃ a b c : X, ∃ p : Path a b, ∃ q : Path b c,
      p.toContinuousMap = x ∧
      q.toContinuousMap = y ∧
      (p.trans q) 1 = z 0) ↔ (x 1 = y 0 ∧ y 1 = z 0) := by
  constructor
  · rintro ⟨a, b, c, p, q, rfl, rfl, h⟩
    refine ⟨?_, ?_⟩
    · simp only [Path.coe_toContinuousMap, Path.source, Path.target]
    · rw [Path.target] at h
      simpa only [Path.coe_toContinuousMap, Path.target] using h
  · rintro ⟨h1, h2⟩
    refine ⟨x 0, x 1, y 1, ⟨x, rfl, rfl⟩, ⟨y, h1.symm, rfl⟩, rfl, rfl, ?_⟩
    rw [Path.target]
    exact h2

theorem claim_rhs_iff_endpoints {X : Type*} [TopologicalSpace X]
    (x y z : ContinuousMap (Set.Icc (0 : ℝ) 1) X) :
    (∃ b c d : X, ∃ q : Path b c, ∃ r : Path c d,
      q.toContinuousMap = y ∧
      r.toContinuousMap = z ∧
      x 1 = (q.trans r) 0) ↔ (x 1 = y 0 ∧ y 1 = z 0) := by
  constructor
  · rintro ⟨b, c, d, q, r, rfl, rfl, h⟩
    refine ⟨?_, ?_⟩
    · rw [Path.source] at h
      simpa only [Path.coe_toContinuousMap, Path.source] using h
    · simp only [Path.coe_toContinuousMap, Path.source, Path.target]
  · rintro ⟨h1, h2⟩
    refine ⟨y 0, y 1, z 1, ⟨y, rfl, rfl⟩, ⟨z, h2.symm, rfl⟩, rfl, rfl, ?_⟩
    rw [Path.source]
    exact h1

/-- Extra: the output's statement itself is true (proved without sorry). -/
theorem claim_statement_true {X : Type*} [TopologicalSpace X]
    (x y z : ContinuousMap (Set.Icc (0 : ℝ) 1) X) :
    (∃ a b c : X, ∃ p : Path a b, ∃ q : Path b c,
      p.toContinuousMap = x ∧
      q.toContinuousMap = y ∧
      (p.trans q) 1 = z 0) ↔
    (∃ b c d : X, ∃ q : Path b c, ∃ r : Path c d,
      q.toContinuousMap = y ∧
      r.toContinuousMap = z ∧
      x 1 = (q.trans r) 0) := by
  rw [claim_lhs_iff_endpoints, claim_rhs_iff_endpoints]
