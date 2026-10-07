-- R's `HasRiemannIntegral` quantifies over partitions that are merely `Monotone`
-- (degenerate subintervals allowed); P's local `HasRiemannIntegral` only over strictly increasing
-- partitions. Otherwise (tags in `Set.Icc` vs. a conjunction, `∀ ε > 0` vs `∀ ε, 0 < ε →`,
-- hypothesis placement) the statements coincide. The two integral predicates are equivalent:
-- strict ⇒ monotone gives one direction; for the other, a degenerate subinterval contributes
-- `f t * 0 = 0` to the Riemann sum and can be deleted without changing the sum or the mesh
-- (induction on the number of subintervals).

/-- P's integral predicate, copied verbatim from P's `let`. -/
def cert_PH (f : ℝ → ℝ) (u v L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ) (p : Fin (n + 1) → ℝ) (t : Fin n → ℝ),
        p 0 = u →
        p (Fin.last n) = v →
        (∀ i : Fin n, p i.castSucc < p i.succ) →
        (∀ i : Fin n, t i ∈ Set.Icc (p i.castSucc) (p i.succ)) →
        (∀ i : Fin n, p i.succ - p i.castSucc < δ) →
        |Finset.sum Finset.univ
            (fun i : Fin n => f (t i) * (p i.succ - p i.castSucc)) - L| < ε

/-- Deleting degenerate subintervals: a bound for strictly increasing partitions gives the
same bound for monotone ones. -/
theorem cert_collapse (f : ℝ → ℝ) (u v L ε δ : ℝ)
    (H : ∀ (n : ℕ) (p : Fin (n + 1) → ℝ) (t : Fin n → ℝ),
      p 0 = u → p (Fin.last n) = v → (∀ i : Fin n, p i.castSucc < p i.succ) →
      (∀ i : Fin n, t i ∈ Set.Icc (p i.castSucc) (p i.succ)) →
      (∀ i : Fin n, p i.succ - p i.castSucc < δ) →
      |Finset.sum Finset.univ (fun i : Fin n => f (t i) * (p i.succ - p i.castSucc)) - L| < ε) :
    ∀ (n : ℕ) (x : Fin (n + 1) → ℝ) (t : Fin n → ℝ),
      x 0 = u → x (Fin.last n) = v → Monotone x →
      (∀ i : Fin n, x i.castSucc ≤ t i ∧ t i ≤ x i.succ) →
      (∀ i : Fin n, x i.succ - x i.castSucc < δ) →
      |(∑ i : Fin n, f (t i) * (x i.succ - x i.castSucc)) - L| < ε := by
  intro n
  induction n with
  | zero =>
    intro x t h0 hl _ ht hd
    exact H 0 x t h0 hl (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
  | succ m ih =>
    intro x t h0 hl hmon ht hd
    by_cases hs : ∀ i : Fin (m + 1), x i.castSucc < x i.succ
    · exact H (m + 1) x t h0 hl hs (fun i => ht i) hd
    · push_neg at hs
      obtain ⟨k, hk⟩ := hs
      have hk' : x k.castSucc = x k.succ :=
        le_antisymm (hmon (Fin.castSucc_le_succ k)) hk
      have hA : ∀ j : Fin m, x (k.castSucc.succAbove j.castSucc) = x (k.succAbove j).castSucc := by
        intro j
        congr 1
        ext
        simp only [Fin.succAbove, Fin.lt_def, Fin.coe_castSucc, Fin.val_succ]
        split_ifs <;> simp only [Fin.coe_castSucc, Fin.val_succ] at * <;> omega
      have hB : ∀ j : Fin m, x (k.castSucc.succAbove j.succ) = x (k.succAbove j).succ := by
        intro j
        by_cases hj : (j : ℕ) + 1 = k
        · have e1 : k.castSucc.succAbove j.succ = k.succ := by
            ext
            simp only [Fin.succAbove, Fin.lt_def, Fin.coe_castSucc, Fin.val_succ]
            split_ifs <;> simp only [Fin.coe_castSucc, Fin.val_succ] at * <;> omega
          have e2 : (k.succAbove j).succ = k.castSucc := by
            ext
            simp only [Fin.succAbove, Fin.lt_def, Fin.coe_castSucc, Fin.val_succ]
            split_ifs <;> simp only [Fin.coe_castSucc, Fin.val_succ] at * <;> omega
          rw [e1, e2, hk']
        · congr 1
          ext
          simp only [Fin.succAbove, Fin.lt_def, Fin.coe_castSucc, Fin.val_succ]
          split_ifs <;> simp only [Fin.coe_castSucc, Fin.val_succ] at * <;> omega
      have h0' : x (k.castSucc.succAbove 0) = u := by
        by_cases hk0 : (k : ℕ) = 0
        · have e1 : k.castSucc.succAbove 0 = k.succ := by
            ext
            simp only [Fin.succAbove, Fin.lt_def, Fin.coe_castSucc, Fin.val_succ, Fin.val_zero]
            split_ifs <;> simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_zero] at * <;> omega
          have e2 : (0 : Fin (m + 2)) = k.castSucc := by
            ext
            simp only [Fin.coe_castSucc, Fin.val_zero]
            omega
          rw [e1, ← hk', ← e2, h0]
        · have e1 : k.castSucc.succAbove 0 = 0 := by
            ext
            simp only [Fin.succAbove, Fin.lt_def, Fin.coe_castSucc, Fin.val_succ, Fin.val_zero]
            split_ifs <;> simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_zero] at * <;> omega
          rw [e1, h0]
      have hl' : x (k.castSucc.succAbove (Fin.last m)) = v := by
        have e1 : k.castSucc.succAbove (Fin.last m) = Fin.last (m + 1) := by
          ext
          simp only [Fin.succAbove, Fin.lt_def, Fin.coe_castSucc, Fin.val_succ, Fin.val_last]
          split_ifs <;> simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_last] at * <;> omega
        rw [e1, hl]
      have hsum : (∑ i : Fin (m + 1), f (t i) * (x i.succ - x i.castSucc)) =
          ∑ j : Fin m, f (t (k.succAbove j)) *
            (x (k.castSucc.succAbove j.succ) - x (k.castSucc.succAbove j.castSucc)) := by
        rw [Fin.sum_univ_succAbove _ k, hk', sub_self, mul_zero, zero_add]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hA, hB]
      rw [hsum]
      refine ih (fun l => x (k.castSucc.succAbove l)) (fun j => t (k.succAbove j)) h0' hl'
        (hmon.comp (Fin.strictMono_succAbove _).monotone) ?_ ?_
      · intro j
        simp only [hA, hB]
        exact ht _
      · intro j
        simp only [hA, hB]
        exact hd _

theorem cert_hiff (f : ℝ → ℝ) (u v L : ℝ) : R.HasRiemannIntegral f u v L ↔ cert_PH f u v L := by
  constructor
  · intro hR ε hε
    obtain ⟨δ, hδ, H⟩ := hR ε hε
    refine ⟨δ, hδ, fun n p t hp0 hpl hps ht hd => ?_⟩
    exact H n p t hp0 hpl (Fin.monotone_iff_le_succ.mpr (fun i => (hps i).le)) ht hd
  · intro hP ε hε
    obtain ⟨δ, hδ, H⟩ := hP ε hε
    exact ⟨δ, hδ, cert_collapse f u v L ε δ H⟩

theorem cert : (type_of% @R.riemannIntegrable_of_limit_subintervals) ↔
    (type_of% @P.riemann_integrable_of_exhaustion) := by
  constructor
  · intro h a b f aS bS hbd hord ha hb HRI hint
    obtain ⟨I, hI, hJ⟩ := h f a b aS bS hbd hord ha hb
      (fun n => by
        obtain ⟨L, hL⟩ := hint n
        exact ⟨L, (cert_hiff f _ _ L).mpr hL⟩)
    exact ⟨I, (cert_hiff f a b I).mp hI,
      fun J hJ' => hJ J (fun n => (cert_hiff f _ _ (J n)).mpr (hJ' n))⟩
  · intro h f a b aS bS hbd hord ha hb hint
    obtain ⟨I, hI, hJ⟩ := h a b f aS bS hbd hord ha hb
      (fun n => by
        obtain ⟨L, hL⟩ := hint n
        exact ⟨L, (cert_hiff f _ _ L).mp hL⟩)
    exact ⟨I, (cert_hiff f a b I).mpr hI,
      fun J hJ' => hJ J (fun n => (cert_hiff f _ _ (J n)).mp (hJ' n))⟩
