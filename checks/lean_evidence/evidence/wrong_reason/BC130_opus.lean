/-! Judge claim: the conclusion `¬ Summable (fun n => a (n+1))` asserts the series is "not summable
at all" rather than "not absolutely summable", and this second conjunct "contradicts the first
hypothesis". In Mathlib, for real sequences `Summable` is unconditional summability, which is
equivalent to absolute summability (`summable_abs_iff`); and it is consistent with convergence of
the partial sums (alternating harmonic series). In fact the output's statement is provable. -/

/-- For ℝ-valued sequences, `¬ Summable` of the output's function is exactly
"not absolutely summable". -/
theorem claim_not_summable_iff_not_abs_summable (a : ℕ → ℝ) :
    ¬ Summable (fun n : ℕ => a (n + 1)) ↔ ¬ Summable (fun n : ℕ => |a (n + 1)|) := by
  rw [summable_abs_iff]

lemma aux_sum_Icc_one_eq_sum_range (g : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, g n = ∑ i ∈ Finset.range N, g (i + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma aux_not_summable_of_abs_div (a : ℕ → ℝ)
    (h_abs_div : ¬ ∃ L : ℝ, Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, |a n|)
      Filter.atTop (nhds L)) :
    ¬ Summable (fun n : ℕ => a (n + 1)) := by
  intro hs
  apply h_abs_div
  refine ⟨∑' n, |a (n + 1)|, ?_⟩
  have h := (summable_abs_iff.mpr hs).hasSum.tendsto_sum_nat
  have e : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, |a n|) =
      fun N => ∑ i ∈ Finset.range N, |a (i + 1)| :=
    funext fun N => aux_sum_Icc_one_eq_sum_range (fun n => |a n|) N
  rw [e]
  exact h

/-- The output's full statement holds (so the second conjunct follows from `h_abs_div`). -/
theorem claim_statement_true (a : ℕ → ℝ)
    (h_conv : ∃ L : ℝ, Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n)
      Filter.atTop (nhds L))
    (h_abs_div : ¬ ∃ L : ℝ, Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, |a n|)
      Filter.atTop (nhds L)) :
    (∃ L : ℝ, Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n)
      Filter.atTop (nhds L)) ∧ ¬ Summable (fun n : ℕ => a (n + 1)) :=
  ⟨h_conv, aux_not_summable_of_abs_div a h_abs_div⟩

/-- The hypotheses and the second conjunct are jointly satisfiable (alternating harmonic
series), so `¬ Summable` does not contradict `h_conv`. -/
theorem claim_hyps_and_not_summable_consistent :
    ∃ a : ℕ → ℝ,
      (∃ L : ℝ, Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n)
        Filter.atTop (nhds L)) ∧
      (¬ ∃ L : ℝ, Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, |a n|)
        Filter.atTop (nhds L)) ∧
      ¬ Summable (fun n : ℕ => a (n + 1)) := by
  set a : ℕ → ℝ := fun n => (-1) ^ n * (1 / ((n : ℝ) + 1)) with ha_def
  -- shift so that a' (n+1) = a n
  let a' : ℕ → ℝ := fun n => (-1) ^ (n + 1) * (1 / (n : ℝ))
  have hshift : ∀ i : ℕ, a' (i + 1) = a i := by
    intro i
    simp only [a', ha_def]
    push_cast
    ring
  have habs : ∀ i : ℕ, |a' (i + 1)| = 1 / ((i : ℝ) + 1) := by
    intro i
    rw [hshift]
    simp only [ha_def, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [abs_of_pos (by positivity)]
  have hdiv : ¬ ∃ L : ℝ, Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, |a' n|)
      Filter.atTop (nhds L) := by
    rintro ⟨L, hL⟩
    have e : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, |a' n|) =
        fun N => ∑ i ∈ Finset.range N, (1 / ((i : ℝ) + 1)) := by
      funext N
      rw [aux_sum_Icc_one_eq_sum_range (fun n => |a' n|) N]
      exact Finset.sum_congr rfl fun i _ => habs i
    rw [e] at hL
    exact not_tendsto_nhds_of_tendsto_atTop Real.tendsto_sum_range_one_div_nat_succ_atTop L hL
  refine ⟨a', ?_, hdiv, aux_not_summable_of_abs_div a' hdiv⟩
  have hanti : Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    intro m n hmn
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hzero : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨l, hl⟩ := hanti.tendsto_alternating_series_of_tendsto_zero hzero
  refine ⟨l, ?_⟩
  have e : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a' n) =
      fun N => ∑ i ∈ Finset.range N, (-1) ^ i * (1 / ((i : ℝ) + 1)) := by
    funext N
    rw [aux_sum_Icc_one_eq_sum_range a' N]
    exact Finset.sum_congr rfl fun i _ => hshift i
  rw [e]
  exact hl
