-- BC046:opus. NOT run by check.py: the anchor contains no `theorem`/`lemma` line (only
-- `private lemma`s and a `def`), so `check.main_thm` raises IndexError on it, and a file named
-- BC046_opus.lean would crash `python3 check.py anchor`. This file is meant to be appended to
-- `namespace R <rejected> end R namespace P <anchor> end P`, exactly as check.py builds it.
--
-- The anchor is a `def` building `Subgroup (GL (Fin n) R)` with carrier = invertible diagonal
-- matrices, for every commutative ring R (its one_mem'/inv_mem' fields use sorried lemmas).
-- Its implicit claim is `PClaim` below. The rejected output R states, over ℝ only,
-- ∃ subgroup with that carrier ∧ the carrier is closed in GL(n, ℝ).

/-- The claim the anchor's `def` encodes. -/
def PClaim : Prop :=
  ∀ (n : ℕ) (S : Type) [DecidableEq S] [CommRing S],
    ∃ H : Subgroup (GL (Fin n) S),
      (H : Set (GL (Fin n) S)) = {M : GL (Fin n) S | (M : Matrix (Fin n) (Fin n) S).IsDiag}

/-- The anchor's claim at the scope of the NL (real matrices). -/
def PClaimReal : Prop :=
  ∀ n : ℕ, ∃ H : Subgroup (GL (Fin n) ℝ),
    (H : Set (GL (Fin n) ℝ)) = {M : GL (Fin n) ℝ | (M : Matrix (Fin n) (Fin n) ℝ).IsDiag}

/-- The extra conjunct of R holds automatically: invertible diagonal matrices are closed in GL. -/
lemma isClosed_diag (n : ℕ) :
    IsClosed {A : GL (Fin n) ℝ | (A : Matrix (Fin n) (Fin n) ℝ).IsDiag} := by
  have hM : IsClosed {M : Matrix (Fin n) (Fin n) ℝ | M.IsDiag} := by
    have : {M : Matrix (Fin n) (Fin n) ℝ | M.IsDiag} =
        ⋂ i, ⋂ j, ⋂ (_ : i ≠ j), {M | M i j = 0} := by
      ext M
      simp [Matrix.IsDiag, Pairwise]
    rw [this]
    refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
    exact isClosed_eq (continuous_id.matrix_elem i j) continuous_const
  exact hM.preimage Units.continuous_val

/-- R is equivalent to the anchor's claim specialized to ℝ; both directions use `h`. -/
theorem cert_real : (type_of% @R.diagonal_matrices_matrix_group) ↔ PClaimReal := by
  constructor
  · intro h n
    obtain ⟨H, hH, _⟩ := h n
    exact ⟨H, hH⟩
  · intro h n
    obtain ⟨H, hH⟩ := h n
    exact ⟨H, hH, hH ▸ isClosed_diag n⟩

/-- The anchor's general claim is true (proved outright, no sorry): this is what the
R → anchor direction would need, and R (about ℝ only) cannot supply it. -/
theorem PClaim_true : PClaim := by
  intro n S _ _
  refine ⟨{ carrier := {M : GL (Fin n) S | (M : Matrix (Fin n) (Fin n) S).IsDiag}
            mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩
  · intro a b ha hb
    have ha' := (Matrix.isDiag_iff_diagonal_diag _).mp ha
    have hb' := (Matrix.isDiag_iff_diagonal_diag _).mp hb
    show ((a * b : GL (Fin n) S) : Matrix (Fin n) (Fin n) S).IsDiag
    rw [Units.val_mul, ← ha', ← hb', Matrix.diagonal_mul_diagonal]
    exact Matrix.isDiag_diagonal _
  · show ((1 : GL (Fin n) S) : Matrix (Fin n) (Fin n) S).IsDiag
    rw [Units.val_one]
    exact Matrix.isDiag_one
  · intro a ha
    have ha' := (Matrix.isDiag_iff_diagonal_diag _).mp ha
    show ((a⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S).IsDiag
    rw [Matrix.coe_units_inv, ← ha', Matrix.inv_diagonal]
    exact Matrix.isDiag_diagonal _

#print axioms isClosed_diag
#print axioms cert_real
#print axioms PClaim_true
