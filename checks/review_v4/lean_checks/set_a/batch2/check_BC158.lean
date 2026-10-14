import Mathlib

open MeasureTheory

/-- The agent's statement with all variables universally quantified. -/
def BC158_stmt : Prop :=
  ∀ {f : ℝ → ℝ} {a b ε : ℝ}, 0 < ε → IntervalIntegrable f volume a b →
    ∃ n : ℕ, ∃ x : Fin (n + 1) → ℝ,
      x 0 = a ∧ x (Fin.last n) = b ∧
      (StrictMono x) ∧
      ∀ c : Fin n → ℝ,
        (∀ k : Fin n, c k ∈ Set.Icc (x (Fin.castSucc k)) (x (Fin.succ k))) →
          |(∫ t in a..b, f t) -
              ∑ k : Fin n, f (c k) * (x (Fin.succ k) - x (Fin.castSucc k))| < ε

/-- Counterexample 1 (no `a ≤ b` hypothesis): f = 0, a = 1, b = 0. -/
theorem BC158_false_reversed : ¬ BC158_stmt := by
  intro h
  obtain ⟨n, x, h0, hl, hmono, -⟩ :=
    @h (fun _ => (0:ℝ)) 1 0 1 one_pos intervalIntegrable_const
  have : x 0 ≤ x (Fin.last n) := hmono.monotone (Fin.zero_le _)
  linarith

lemma tele (n : ℕ) (x : Fin (n+1) → ℝ) :
    ∑ k : Fin n, (x k.succ - x k.castSucc) = x (Fin.last n) - x 0 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    have := ih (fun i => x i.castSucc)
    simp only at this
    simp only [Fin.succ_castSucc]
    rw [this]
    simp only [Fin.succ_last, Fin.castSucc_zero]
    ring

/-- Counterexample 2 (Lebesgue vs Riemann integrability): the Dirichlet function on [0,1]. -/
theorem BC158_false_dirichlet : ¬ BC158_stmt := by
  intro h
  set S : Set ℝ := Set.range ((↑) : ℚ → ℝ) with hSdef
  have hS : volume S = 0 := (Set.countable_range _).measure_zero volume
  set f : ℝ → ℝ := S.indicator 1 with hfdef
  have hf0 : f =ᵐ[volume] 0 := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun t ht => ?_) hS
    by_contra hn
    exact ht (by simp [hfdef, Set.indicator_of_notMem hn])
  have hint : IntervalIntegrable f volume 0 1 := by
    have h0 : IntervalIntegrable (fun _ => (0:ℝ)) volume 0 1 := intervalIntegrable_const
    exact h0.congr (ae_restrict_of_ae hf0.symm)
  have hI : (∫ t in (0:ℝ)..1, f t) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0:ℝ)) (hf0.mono (fun t ht _ => ht))]
    simp
  obtain ⟨n, x, h0, hl, hmono, hc⟩ := @h f 0 1 (1/2) (by norm_num) hint
  have hq : ∀ k : Fin n, ∃ q : ℚ, x k.castSucc < q ∧ (q : ℝ) < x k.succ :=
    fun k => exists_rat_btwn (hmono (Fin.castSucc_lt_succ k))
  choose q hq using hq
  have hsum := hc (fun k => (q k : ℝ)) (fun k => ⟨(hq k).1.le, (hq k).2.le⟩)
  have hf1 : ∀ k : Fin n, f (q k) = 1 := fun k => by
    simp [hfdef, hSdef]
  simp only [hf1, one_mul, tele, h0, hl, hI] at hsum
  norm_num at hsum

#print axioms BC158_false_reversed
#print axioms BC158_false_dirichlet
