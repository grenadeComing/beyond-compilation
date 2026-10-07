-- NOT EQUIVALENT (different integration theories). No `cert` is given.
-- R (rejected): Riemann integrability via its own `HasRiemannIntegral` (tagged partitions, mesh → 0),
--   f bounded on [a,b]; hypothesis and conclusion are Riemann integrability on [aₙ,bₙ] / [a,b].
-- P (anchor): `IntervalIntegrable f volume` (Lebesgue integrability) on [aₙ,bₙ] / [a,b], with f
--   bounded on all of ℝ, and the Lebesgue interval integrals converge.
-- Both theorems are true, so `R ↔ P` could only be "proved" by proving each outright, which the
-- checker's rule (d) forbids. Neither follows from the other by matching hypotheses:
-- the claims below show the integrability notions differ. The Dirichlet function is Lebesgue
-- (interval) integrable on [0,1] but has no `R.HasRiemannIntegral` on [0,1]; so e.g. with
-- aₙ = 1/(n+3), bₙ = 1 - 1/(n+3) it satisfies every hypothesis of P while R's hypothesis
-- `hint` fails, and P's conclusion never supplies R's conclusion (Riemann integrability on [a,b]).

open Classical in
noncomputable def dirichlet (x : ℝ) : ℝ := if ∃ q : ℚ, (q : ℝ) = x then 1 else 0

theorem claim_dirichlet_intervalIntegrable :
    IntervalIntegrable dirichlet MeasureTheory.volume 0 1 := by
  have hnull : MeasureTheory.volume (Set.range ((↑) : ℚ → ℝ)) = 0 :=
    (Set.countable_range _).measure_zero _
  have hae : (0 : ℝ → ℝ) =ᵐ[MeasureTheory.volume] dirichlet := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ hnull
    intro x hx
    simp only [Set.mem_setOf_eq, Pi.zero_apply, dirichlet] at hx
    split_ifs at hx with hq
    · exact hq
    · exact absurd rfl hx
  exact ((MeasureTheory.integrable_zero ℝ ℝ _).congr hae).intervalIntegrable

theorem claim_dirichlet_not_riemann : ¬ ∃ I, R.HasRiemannIntegral dirichlet 0 1 I := by
  rintro ⟨I, hI⟩
  obtain ⟨δ, hδ, hδI⟩ := hI (1 / 2) (by norm_num)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  have hNpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  let x : Fin (m + 1 + 1) → ℝ := fun i => ((i : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)
  have hx0 : x 0 = 0 := by simp [x]
  have hxl : x (Fin.last (m + 1)) = 1 := by
    simp only [x, Fin.val_last]
    exact div_self hNpos.ne'
  have hmono : Monotone x := by
    intro i j hij
    simp only [x]
    gcongr
    exact_mod_cast hij
  have hstep : ∀ i : Fin (m + 1), x i.succ - x i.castSucc = 1 / ((m + 1 : ℕ) : ℝ) := by
    intro i
    simp only [x, Fin.val_succ, Fin.coe_castSucc]
    push_cast
    ring
  have hmesh : ∀ i : Fin (m + 1), x i.succ - x i.castSucc < δ := by
    intro i
    rw [hstep]
    push_cast
    exact hm
  -- rational tags: every Riemann sum equals 1
  have h1 := hδI (m + 1) x (fun i => x i.castSucc) hx0 hxl hmono
    (fun i => ⟨le_rfl, hmono (Fin.castSucc_le_succ i)⟩) hmesh
  -- irrational tags: every Riemann sum equals 0
  set c : ℝ := Real.sqrt 2 / ((2 * (m + 1) : ℕ) : ℝ) with hc
  have hcirr : Irrational c := irrational_sqrt_two.div_natCast (by omega)
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 / ((m + 1 : ℕ) : ℝ) := by
    have hs : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    rw [hc, div_le_div_iff₀ (by positivity) hNpos]
    push_cast
    nlinarith
  have h2 := hδI (m + 1) x (fun i => x i.castSucc + c) hx0 hxl hmono
    (fun i => ⟨by linarith, by have := hstep i; linarith⟩) hmesh
  have hs1 : ∑ i : Fin (m + 1), dirichlet (x i.castSucc) * (x i.succ - x i.castSucc) = 1 := by
    have hd : ∀ i : Fin (m + 1), dirichlet (x i.castSucc) = 1 := by
      intro i
      simp only [dirichlet]
      rw [if_pos]
      exact ⟨((i : ℕ) : ℚ) / ((m + 1 : ℕ) : ℚ), by simp [x]⟩
    simp only [hd, hstep, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have hs2 : ∑ i : Fin (m + 1), dirichlet (x i.castSucc + c) * (x i.succ - x i.castSucc) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hd : dirichlet (x i.castSucc + c) = 0 := by
      simp only [dirichlet]
      rw [if_neg]
      rintro ⟨q, hq⟩
      have hirr : Irrational (c + ((((i : ℕ) : ℚ) / ((m + 1 : ℕ) : ℚ) : ℚ) : ℝ)) :=
        hcirr.add_ratCast _
      apply hirr
      refine ⟨q, ?_⟩
      rw [hq]
      simp [x]
      ring
    rw [hd, zero_mul]
  simp only at h1 h2
  rw [hs1] at h1
  rw [hs2] at h2
  have e1 := abs_sub_lt_iff.mp h1
  have e2 := abs_sub_lt_iff.mp h2
  linarith

#print axioms claim_dirichlet_intervalIntegrable
#print axioms claim_dirichlet_not_riemann
