-- R: for real matrices indexed by Fin n, {A | AᵀA = 1} = {A | IsUnit A ∧ AAᵀ = 1}.
-- P: for every finite index type n and every commutative ring R, O(n,R) = {A | AAᵀ = 1}.
-- P → R holds from h (instance n := Fin n, R := ℝ). R → P does NOT follow from R: P quantifies
-- over all commutative rings, R only speaks about ℝ. The direction below is therefore proved
-- outright (P is Mathlib's `Matrix.mem_orthogonalGroup_iff`) WITHOUT using h, so this `cert`
-- must not count as verified. `cert_real` shows R is equivalent to P specialized to ℝ, Fin n.
-- Note: check.py cannot locate the anchor theorem: its name is «srdoty_alg_linear-gps_366»
-- (guillemets, contains '-'), and the regex keeps the guillemets, so it reports
-- "@@MATCH missing P theorem". `cert` is stated with P at universes {0, 0}.

theorem cert : (type_of% @R.orthogonal_group_eq) ↔
    (type_of% @P.«srdoty_alg_linear-gps_366».{0, 0}) := by
  constructor
  · intro _h
    -- not derivable from R; proved outright
    intro n _ _ S _
    ext A
    exact Matrix.mem_orthogonalGroup_iff n S
  · intro h
    intro n
    ext A
    have hA := Set.ext_iff.mp (h (Fin n) ℝ) A
    have hAt := Set.ext_iff.mp (h (Fin n) ℝ) A.transpose
    simp only [SetLike.mem_coe, Set.mem_setOf_eq, Matrix.transpose_transpose] at hA hAt
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h1
      have h2 : A * A.transpose = 1 := hA.mp ((Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mpr h1)
      exact ⟨⟨⟨A, A.transpose, h2, h1⟩, rfl⟩, h2⟩
    · rintro ⟨_, h2⟩
      exact (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp (hA.mpr h2)

/-- The anchor's statement specialized to the scope of the NL (real matrices, index Fin n). -/
def PReal : Prop :=
  ∀ n : ℕ, (Matrix.orthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) =
    {A | A * A.transpose = 1}

theorem cert_real : (type_of% @R.orthogonal_group_eq) ↔ PReal := by
  constructor
  · intro h
    intro n
    ext A
    have hR := Set.ext_iff.mp (h n) A
    simp only [Set.mem_setOf_eq] at hR
    simp only [SetLike.mem_coe, Set.mem_setOf_eq, Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ]
    constructor
    · intro h1
      exact (hR.mp h1).2
    · intro h2
      exact hR.mpr ⟨⟨⟨A, A.transpose, h2, Matrix.mul_eq_one_comm.mp h2⟩, rfl⟩, h2⟩
  · intro h
    intro n
    ext A
    have hA := Set.ext_iff.mp (h n) A
    simp only [SetLike.mem_coe, Set.mem_setOf_eq] at hA
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h1
      have h2 : A * A.transpose = 1 := hA.mp ((Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mpr h1)
      exact ⟨⟨⟨A, A.transpose, h2, h1⟩, rfl⟩, h2⟩
    · rintro ⟨_, h2⟩
      exact (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp (hA.mpr h2)

#print axioms cert_real
