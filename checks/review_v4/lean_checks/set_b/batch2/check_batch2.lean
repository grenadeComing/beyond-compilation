import Mathlib

open Matrix

-- BC088 kimina_autof: elaboration of `•` between rows/columns
set_option pp.coercions false in
#check fun (A : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) => (Aᵀ i) • (A j) = if i = j then 1 else 0

-- BC088 kimina_autof statement is false for n = 2 (A = 1, i = j = 0, evaluate at index 1)
example : ¬ (∀ (A : Matrix (Fin 2) (Fin 2) ℝ), (∀ i j, A i j = if i = j then 1 else 0) →
    ∀ i j, (Aᵀ i) • (A j) = if i = j then 1 else 0) := by
  intro h
  have h1 := congrFun (h 1 (fun i j => Matrix.one_apply) 0 0) 1
  simp [Matrix.one_apply] at h1

-- BC088 goedel_prover: entry (i,j) of Aᵀ * A is the dot product of columns i and j
example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (Aᵀ * A) i j = (fun k => A k i) ⬝ᵥ (fun k => A k j) := rfl
example {n : ℕ} (i j : Fin n) : (1 : Matrix (Fin n) (Fin n) ℝ) i j = if i = j then 1 else 0 :=
  Matrix.one_apply

-- BC100 kimina_prover: hypotheses inconsistent for MonoidWithZeroHom
example (f : ℂ →*₀ ℂ) (hf2 : f 0 = 1) : False := by
  rw [map_zero] at hf2; exact zero_ne_one hf2

-- BC108 herald: injectivity hypothesis is self-contradictory
example {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ U) (hf_inj : ∀ w ∈ U, f w ≠ f z) : False :=
  hf_inj z hz rfl

-- BC223 goedel_prover: what `A ∩ S` with `S : Set A` elaborates to
set_option pp.coercions false in
#check fun (X : Type) [TopologicalSpace X] (A : Set X) (S : Set A) => A ∩ S

-- BC014 herald: RHS is false in any domain, so the statement asserts ¬ IsField R
example {R : Type*} [CommRing R] [IsDomain R] : ¬ ∀ (r : Rˣ), (r : R) = 0 :=
  fun h => one_ne_zero (h 1)
example : ¬ (IsField ℚ ↔ ∀ (r : ℚˣ), (r : ℚ) = 0) := by
  intro h
  exact one_ne_zero ((h.mp (Field.toIsField ℚ)) 1)

-- BC223 herald: false instance: A = Ioo 0 2, S = {x | x ≤ 1} in A
example : ¬ (∀ (A : Set ℝ) (S : Set A), IsClosed S ↔ IsClosed (Subtype.val '' S)) := by
  intro h
  have hS : IsClosed {x : Set.Ioo (0:ℝ) 2 | (x : ℝ) ≤ 1} :=
    isClosed_le continuous_subtype_val continuous_const
  have h2 := (h (Set.Ioo 0 2) _).mp hS
  have himg : Subtype.val '' {x : Set.Ioo (0:ℝ) 2 | (x : ℝ) ≤ 1} = Set.Ioc 0 1 := by
    ext y; constructor
    · rintro ⟨⟨x, hx1, hx2⟩, hx, rfl⟩; exact ⟨hx1, hx⟩
    · rintro ⟨hy1, hy2⟩; exact ⟨⟨y, hy1, by linarith⟩, hy2, rfl⟩
  rw [himg] at h2
  have : (0:ℝ) ∈ Set.Ioc (0:ℝ) 1 := by
    have hc : closure (Set.Ioc (0:ℝ) 1) = Set.Icc 0 1 := closure_Ioc (by norm_num)
    rw [← h2.closure_eq, hc]; exact ⟨le_refl _, by norm_num⟩
  exact (lt_irrefl _ this.1)
