import Mathlib

open Topology Filter

theorem kimina_stmt
(x : ℕ → ℝ)
(h_bdd : ∃ B, ∀ n, |x n| ≤ B)
(h_lim : ∃ L, Tendsto x atTop (𝓝 L))
: Tendsto x atTop (𝓝 L) :=
sorry

#check @kimina_stmt

-- L is an auto-bound implicit universally quantified variable, so the statement is false:
example : ¬ (∀ (L : ℝ) (x : ℕ → ℝ), (∃ B, ∀ n, |x n| ≤ B) → (∃ L', Tendsto x atTop (𝓝 L')) →
    Tendsto x atTop (𝓝 L)) := by
  intro h
  have h1 := h 1 (fun _ => 0) ⟨0, by simp⟩ ⟨0, tendsto_const_nhds⟩
  have h0 : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have := tendsto_nhds_unique h1 h0
  norm_num at this
