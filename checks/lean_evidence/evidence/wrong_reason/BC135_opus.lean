/-! Judge claim: the output "does not use Mathlib's standard `RiemannIntegrable`/`Integral`
predicates" and "quantifies over a specific class of (grid) partitions rather than arbitrary
tagged partitions". Whether grid partitions are the right notion is a question about the textbook
definition (not checkable here). Supporting facts checked below: (1) Mathlib's Riemann
integral is `BoxIntegral` over `BoxIntegral.Box`, and every such box has all sides of positive
length, so it cannot even represent a rectangle with a side of length 0; (2) the output's
statement is true. -/

/-- Every Mathlib `BoxIntegral.Box` is non-degenerate in every coordinate. -/
theorem claim_mathlib_box_sides_positive (n : ℕ) (I : BoxIntegral.Box (Fin n)) (i : Fin n) :
    I.lower i < I.upper i :=
  I.lower_lt_upper i

/-- Hence no Mathlib box has a side of length 0. -/
theorem claim_no_degenerate_mathlib_box (n : ℕ) (a b : Fin n → ℝ) (i₀ : Fin n)
    (hi₀ : a i₀ = b i₀) : ¬ ∃ I : BoxIntegral.Box (Fin n), I.lower = a ∧ I.upper = b := by
  rintro ⟨I, rfl, rfl⟩
  exact (I.lower_lt_upper i₀).ne hi₀

/-- The output's statement holds (proved without sorry). -/
theorem claim_statement_true
    (n : ℕ) (a b : Fin n → ℝ) (hab : a ≤ b) (i₀ : Fin n) (hi₀ : a i₀ = b i₀)
    (f : (Fin n → ℝ) → ℝ) (hf : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    ∀ ε > 0, ∃ δ > 0, ∀ (k : Fin n → ℕ) (x : (i : Fin n) → Fin (k i + 1) → ℝ),
      (∀ i, Monotone (x i)) →
      (∀ i, x i 0 = a i) →
      (∀ i, x i (Fin.last (k i)) = b i) →
      (∀ i (j : Fin (k i)), x i j.succ - x i j.castSucc < δ) →
      ∀ t : ((i : Fin n) → Fin (k i)) → (Fin n → ℝ),
        (∀ J i, t J i ∈ Set.Icc (x i (J i).castSucc) (x i (J i).succ)) →
        |∑ J, f (t J) * ∏ i, (x i (J i).succ - x i (J i).castSucc)| < ε := by
  intro ε hε
  refine ⟨1, one_pos, ?_⟩
  intro k x hmono h0 hlast _ t _
  have hconst : ∀ j : Fin (k i₀ + 1), x i₀ j = a i₀ := by
    intro j
    apply le_antisymm
    · calc x i₀ j ≤ x i₀ (Fin.last _) := hmono i₀ (Fin.le_last j)
        _ = a i₀ := by rw [hlast, hi₀]
    · calc a i₀ = x i₀ 0 := (h0 i₀).symm
        _ ≤ x i₀ j := hmono i₀ (Fin.zero_le j)
  have hzero : ∀ J : (i : Fin n) → Fin (k i),
      ∏ i, (x i (J i).succ - x i (J i).castSucc) = 0 := by
    intro J
    apply Finset.prod_eq_zero (Finset.mem_univ i₀)
    rw [hconst, hconst, sub_self]
  simp only [hzero, mul_zero, Finset.sum_const_zero, abs_zero]
  exact hε
