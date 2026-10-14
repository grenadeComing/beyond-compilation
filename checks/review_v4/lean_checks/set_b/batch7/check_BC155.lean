import Mathlib

-- kimina_autof statement is false: R = ∅ (closed), f = 0; no E ⊂ ∅ (strict subset) exists.
example : ¬ (∀ {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (R : Set (EuclideanSpace ℝ (Fin n))) (hR : IsClosed R) (hf : ∀ x ∈ R, f x ≥ 0)
    (hRint : ∫ x in R, f x = 0),
    ∃ E ⊂ R, (MeasureTheory.volume E).toReal = 0 ∧ ∀ x ∈ R \ E, f x = 0) := by
  intro h
  obtain ⟨E, hE, -⟩ := @h 1 (fun _ => 0) ∅ isClosed_empty (by simp) (by simp)
  exact hE.2 (Set.empty_subset E)

-- also false for a degenerate closed rectangle R = {0} (allowed by Lebl) with f = 1
example : ¬ (∀ {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (R : Set (EuclideanSpace ℝ (Fin n))) (hR : IsClosed R) (hf : ∀ x ∈ R, f x ≥ 0)
    (hRint : ∫ x in R, f x = 0),
    ∃ E ⊂ R, (MeasureTheory.volume E).toReal = 0 ∧ ∀ x ∈ R \ E, f x = 0) := by
  intro h
  obtain ⟨E, hE, -, h2⟩ := @h 1 (fun _ => 1) {0} isClosed_singleton (by simp)
    (by simp [MeasureTheory.Measure.restrict_singleton])
  have hE0 : E = ∅ := Set.ssubset_singleton_iff.mp hE
  have := h2 0 (by simp [hE0])
  simp at this
