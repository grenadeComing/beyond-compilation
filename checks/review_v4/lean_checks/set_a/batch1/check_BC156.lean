import Mathlib

open Set MeasureTheory ENNReal

def IsOpenBox {n : ℕ} (R : Set (Fin n → ℝ)) : Prop :=
  ∃ (a b : Fin n → ℝ), (∀ i, a i < b i) ∧ R = Set.pi univ (fun i => Set.Ioo (a i) (b i))

noncomputable def mStar {n : ℕ} (S : Set (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨅ (R : ℕ → Set (Fin n → ℝ)) (_ : ∀ j, IsOpenBox (R j)) (_ : S ⊆ ⋃ j, R j),
    ∑' j, volume (R j)

noncomputable def muStar {n : ℕ} (S : Set (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨅ (T : Set ℕ) (R : ↥T → Set (Fin n → ℝ)) (_ : ∀ j, IsOpenBox (R j)) (_ : S ⊆ ⋃ j, R j),
    ∑' j, volume (R j)

-- In dimension 0 every open box has volume 1.
lemma box_vol0 {R : Set (Fin 0 → ℝ)} (h : IsOpenBox R) : volume R = 1 := by
  obtain ⟨a, b, -, rfl⟩ := h
  rw [Real.volume_pi_Ioo]
  simp

-- n = 0: mStar ∅ = ⊤ but muStar ∅ = 0, so the hypothesis `0 < n` is necessary.
example : mStar (∅ : Set (Fin 0 → ℝ)) = ⊤ := by
  unfold mStar
  refine eq_top_iff.mpr (le_iInf fun R => le_iInf fun hR => le_iInf fun _ => ?_)
  have : (fun j => volume (R j)) = fun _ => (1 : ℝ≥0∞) := funext fun j => box_vol0 (hR j)
  rw [this, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]

example : muStar (∅ : Set (Fin 0 → ℝ)) = 0 := by
  unfold muStar
  refine le_antisymm ?_ (zero_le _)
  refine iInf_le_of_le (∅ : Set ℕ) (iInf_le_of_le (fun _ => ∅) (iInf_le_of_le ?_ (iInf_le_of_le ?_ ?_)))
  · rintro ⟨j, hj⟩; exact absurd hj (Set.notMem_empty j)
  · exact Set.empty_subset _
  · simp
