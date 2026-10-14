import Mathlib

open Complex Filter
open scoped Topology

-- The kimina_autof statement (no positive-radius hypothesis) is FALSE: a_k = k!, z_n = 1/(n+1).
example : ¬ (∀ (f : ℂ → ℂ) (a : ℕ → ℂ) (z : ℕ → ℂ),
    (∀ w, f w = ∑' k : ℕ, a k * w ^ k) → (∃ c, Tendsto z atTop (𝓝 c)) → (∀ n, z n ≠ 0) →
    Tendsto z atTop (𝓝 0) → (∀ n, f (z n) = 0) → ∀ k, a k = 0) := by
  intro H
  have hns : ∀ w : ℂ, w ≠ 0 → ¬ Summable (fun k : ℕ => (k.factorial : ℂ) * w ^ k) := by
    intro w hw hs
    have h1 := hs.tendsto_atTop_zero.norm
    simp only [norm_zero] at h1
    have h2 : Tendsto (fun k : ℕ => ‖w‖⁻¹ ^ k / (k.factorial : ℝ)) atTop (𝓝 0) := by
      exact (Real.summable_pow_div_factorial _).tendsto_atTop_zero
    have h3 := h1.mul h2
    rw [zero_mul] at h3
    have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    have h4 : (fun k : ℕ => ‖(k.factorial : ℂ) * w ^ k‖ * (‖w‖⁻¹ ^ k / (k.factorial : ℝ)))
        = fun _ => (1:ℝ) := by
      funext k
      have hf : (k.factorial : ℝ) ≠ 0 := by positivity
      simp only [norm_mul, norm_pow, Complex.norm_natCast]
      field_simp
      ring
    rw [h4] at h3
    have := tendsto_nhds_unique h3 tendsto_const_nhds
    norm_num at this
  have hz : Tendsto (fun n : ℕ => ((1 / ((n:ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [Function.comp_def] using this
  have hz0 : ∀ n : ℕ, ((1 / ((n:ℝ) + 1) : ℝ) : ℂ) ≠ 0 := by
    intro n
    have : (1 / ((n:ℝ) + 1)) ≠ 0 := by positivity
    exact_mod_cast this
  have := H (fun w => ∑' k : ℕ, (k.factorial : ℂ) * w ^ k) (fun k => (k.factorial : ℂ))
    (fun n => ((1 / ((n:ℝ) + 1) : ℝ) : ℂ)) (fun w => rfl) ⟨0, hz⟩ hz0 hz
    (fun n => tsum_eq_zero_of_not_summable (hns _ (hz0 n))) 0
  simp at this
