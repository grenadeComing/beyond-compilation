import Mathlib

open scoped Topology
open Filter

-- The agent's statement (BC148) is false when b < a: Icc a b = ∅ makes uniform convergence vacuous.
example : ¬ (∀ {a b : ℝ} {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ},
    (∀ n, IntervalIntegrable (F n) MeasureTheory.volume a b) →
    TendstoUniformlyOn F f Filter.atTop (Set.Icc a b) →
    IntervalIntegrable f MeasureTheory.volume a b ∧
      Filter.Tendsto (fun n => ∫ x in a..b, F n x) Filter.atTop (𝓝 (∫ x in a..b, f x))) := by
  intro h
  have h1 := (h (a := 1) (b := 0) (F := fun _ _ => (0:ℝ)) (f := fun _ => (1:ℝ))
    (fun n => intervalIntegrable_const) (by
      have : Set.Icc (1:ℝ) 0 = ∅ := Set.Icc_eq_empty (by norm_num)
      rw [this]; exact tendstoUniformlyOn_empty)).2
  -- h1 : Tendsto (fun _ => 0) atTop (𝓝 (∫ x in 1..0, 1)) = 𝓝 (-1); simp derives False
  simp at h1
