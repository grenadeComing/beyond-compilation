import Mathlib

open Filter Topology Nat

-- Counterexample to the agent's statement: a k = k!, z n = 1/(n+1).
-- ∑ k! z^k diverges for every z ≠ 0, so the tsum is 0 by convention, yet a 0 = 1 ≠ 0.
example : ∃ (a z : ℕ → ℂ), Tendsto z atTop (𝓝 0) ∧ (∀ n, z n ≠ 0) ∧
    (∀ n, (∑' k : ℕ, a k * (z n) ^ k) = 0) ∧ ¬ (∀ k, a k = 0) := by
  refine ⟨fun k => (k ! : ℂ), fun n => (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [Function.comp_def] using this
  · intro n
    have : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simpa using this
  · intro n
    apply tsum_eq_zero_of_not_summable
    intro hs
    have h1 := tendsto_zero_iff_norm_tendsto_zero.mp hs.tendsto_atTop_zero
    have h2 := FloorSemiring.tendsto_pow_div_factorial_atTop ((n : ℝ) + 1)
    have h3 := h2.mul h1
    simp only [mul_zero] at h3
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h4 : (fun k : ℕ => ((n : ℝ) + 1) ^ k / (k ! : ℝ) *
        ‖(k ! : ℂ) * ((((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ)) ^ k‖) = fun _ => (1 : ℝ) := by
      funext k
      have hk : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
      rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))]
      rw [div_pow, one_pow]
      field_simp
    rw [h4] at h3
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h3)
  · intro h
    have := h 0
    simp at this
