import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem jirilebl_ra_ch_der_1129 {f : ℝ → ℝ}
  (a b c L : ℝ)
  (h₁ : a < b)
  (h₂ : c ∈ Set.Ioo a b)
  (h₃ : ContinuousOn f (Set.Ioo a b))
  (h₄ : DifferentiableOn ℝ f (Set.Ioo a b \ {c}))
  (h₅ : ∃ l, Tendsto (λ x => deriv f x) (𝓝 c) (𝓝 l)) :
  DifferentiableAt ℝ f c ∧ deriv f c = l :=
sorry

#check @jirilebl_ra_ch_der_1129

-- the herald hypotheses admit a counterexample: f = indicator of {0}, c = 0, d = 1
example : ¬ HasDerivAt (fun x : ℝ => if x = 0 then (1:ℝ) else 0) 0 0 := by
  intro h
  have := h.continuousAt
  have h2 : Tendsto (fun x : ℝ => if x = 0 then (1:ℝ) else 0) (𝓝[≠] 0) (𝓝 1) := by
    simpa using this.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have h3 : Tendsto (fun x : ℝ => if x = 0 then (1:ℝ) else 0) (𝓝[≠] 0) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    simp [hx]
  exact one_ne_zero (tendsto_nhds_unique h2 h3)

-- 𝓝 c (unpunctured) forces deriv f c = l
example (g : ℝ → ℝ) (c l : ℝ) (h : Tendsto g (𝓝 c) (𝓝 l)) : g c = l :=
  tendsto_nhds_unique (tendsto_pure_nhds g c) (h.mono_left (pure_le_nhds c))
