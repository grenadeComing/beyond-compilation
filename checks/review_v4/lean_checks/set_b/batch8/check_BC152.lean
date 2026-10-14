import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset

theorem kimina_bc152
  (x : ℕ → ℝ)
  (hconv : ∃ y, Tendsto x atTop (𝓝 y))
  (hmono : Monotone x)
  (hk : ∃ k, Tendsto x atTop (𝓝 (x k)))
  : ∀ n ≥ k, x n = x k := by sorry

#check @kimina_bc152

-- counterexample to kimina's statement: x = (0,1,1,1,...), k = 0
example : ¬ (∀ (k : ℕ) (x : ℕ → ℝ), (∃ y, Tendsto x atTop (𝓝 y)) → Monotone x →
    (∃ j, Tendsto x atTop (𝓝 (x j))) → ∀ n ≥ k, x n = x k) := by
  intro h
  have := h 0 (fun n => if n = 0 then 0 else 1) ⟨1, ?_⟩ ?_ ⟨1, ?_⟩ 1 (by norm_num)
  · simp at this
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [show n ≠ 0 by omega]
  · intro a b hab
    simp only
    split_ifs <;> norm_num
    omega
  · simp only [one_ne_zero, if_false]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [show n ≠ 0 by omega]

theorem goedel_bc152 (x : ℕ → ℝ) (h : ∃ (k : ℕ), ∀ (n : ℕ), x n = x k) : ∀ (n : ℕ), n ≥ k → x n = x k := by sorry

#check @goedel_bc152

-- ℝ is not a CompleteLinearOrder (Herald's typeclass)
#synth ConditionallyCompleteLinearOrder ℝ
example : ¬ Nonempty (CompleteLinearOrder ℝ) := by
  rintro ⟨inst⟩
  sorry
