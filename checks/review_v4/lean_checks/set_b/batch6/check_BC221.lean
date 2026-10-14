import Mathlib
open Topology TopologicalSpace Set Filter Function

lemma continuous_quotient_lift_tac_19238 [TopologicalSpace X] [TopologicalSpace Y] (q : X → Quotient s₁) (h : Quotient s₁ → Y) : (∀ (x₁ x₂ : X), s₁ x₁ x₂ → h (q x₁) = h (q x₂)) → Continuous (h ∘ q) := sorry

#check @continuous_quotient_lift_tac_19238

-- The herald statement is false: with s = equality setoid on ℝ, q = Quotient.mk, the hypothesis is
-- automatic and h ∘ q can be the (discontinuous) indicator of {0}.
example : ¬ (∀ (s : Setoid ℝ) (q : ℝ → Quotient s) (h : Quotient s → ℝ),
    (∀ x₁ x₂, s x₁ x₂ → h (q x₁) = h (q x₂)) → Continuous (h ∘ q)) := by
  intro H
  let s : Setoid ℝ := ⟨(· = ·), ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩
  let g : ℝ → ℝ := fun x => if x = 0 then 1 else 0
  have hc := H s (Quotient.mk s) (Quotient.lift g (by intro a b hab; exact congrArg g hab))
    (by intro x₁ x₂ hx; exact congrArg _ (Quotient.sound hx))
  have hc' : Continuous g := hc
  have := (Metric.continuous_iff.mp hc') 0 (1/2) (by norm_num)
  obtain ⟨δ, hδ, hball⟩ := this
  have hx := hball (δ/2) (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
  have hne : δ / 2 ≠ 0 := by positivity
  simp [g, hne, Real.dist_eq] at hx
  norm_num at hx
