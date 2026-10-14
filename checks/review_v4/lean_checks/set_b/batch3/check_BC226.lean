import Mathlib

-- Counterexample: f : Unit → ℝ constant 0 (continuous), A = Ioo 0 1.
-- f⁻¹ A = ∅ (closed, closure ∅ = ∅), f⁻¹ (closure A) = f⁻¹ (Icc 0 1) = univ.

-- (1) The NL statement (equality version) is false.
example : ¬ (∀ (f : Unit → ℝ), Continuous f ↔
    ∀ A : Set ℝ, closure (f ⁻¹' A) = f ⁻¹' (closure A)) := by
  intro h
  have h1 := (h (fun _ => (0:ℝ))).1 continuous_const (Set.Ioo 0 1)
  rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] at h1
  have h2 : (fun _ : Unit => (0:ℝ)) ⁻¹' Set.Ioo 0 1 = ∅ := by ext; simp
  have h3 : (fun _ : Unit => (0:ℝ)) ⁻¹' Set.Icc 0 1 = Set.univ := by ext; simp
  rw [h2, h3, closure_empty] at h1
  exact Set.empty_ne_univ h1

-- (2) GPT-5.2's Lean statement is also false (same counterexample).
example : ¬ (∀ (f : Unit → ℝ), Continuous f ↔
    ∀ A : Set ℝ, IsClosed (f ⁻¹' A) → f ⁻¹' (closure A) = f ⁻¹' A) := by
  intro h
  have h2 : (fun _ : Unit => (0:ℝ)) ⁻¹' Set.Ioo 0 1 = ∅ := by ext; simp
  have h1 := (h (fun _ => (0:ℝ))).1 continuous_const (Set.Ioo 0 1) (by rw [h2]; exact isClosed_empty)
  rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] at h1
  have h3 : (fun _ : Unit => (0:ℝ)) ⁻¹' Set.Icc 0 1 = Set.univ := by ext; simp
  rw [h2, h3] at h1
  exact Set.empty_ne_univ h1.symm

-- (3) The correct version (subset) is Mathlib's continuous_iff_closure_preimage_subset-type fact.
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ A : Set Y, closure (f ⁻¹' A) ⊆ f ⁻¹' (closure A) := by
  constructor
  · intro hf A; exact hf.closure_preimage_subset A
  · intro h
    rw [continuous_iff_isClosed]
    intro C hC
    apply closure_subset_iff_isClosed.mp
    have := h C
    rwa [hC.closure_eq] at this
