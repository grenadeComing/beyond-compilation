-- R works on `EuclideanSpace ℝ (Fin n)` with `volume Y`; P works on `Fin n → ℝ` with
-- `volume.toOuterMeasure Y`. `μ s` is by definition `μ.toOuterMeasure s`, and the canonical
-- equivalence `EuclideanSpace ℝ (Fin n) ≃ᵐ (Fin n → ℝ)` is volume preserving, so preimages
-- transport the hypothesis and the conclusion (for arbitrary, possibly non-measurable sets).
open MeasureTheory in
theorem cert : (type_of% @R.outer_measure_zero_of_small_supersets) ↔
    (type_of% @P.jirilebl_ra_ch_multivar_int_1932) := by
  constructor
  · intro h
    intro n X hX
    have hp := EuclideanSpace.volume_preserving_measurableEquiv (Fin n)
    have key := h n (EuclideanSpace.measurableEquiv (Fin n) ⁻¹' X) (by
      intro ε hε
      obtain ⟨Y, hXY, hY⟩ := hX ε hε
      refine ⟨EuclideanSpace.measurableEquiv (Fin n) ⁻¹' Y, Set.preimage_mono hXY, ?_⟩
      rw [hp.measure_preimage_equiv]
      simpa only [Measure.coe_toOuterMeasure] using hY)
    rw [hp.measure_preimage_equiv] at key
    simpa only [Measure.coe_toOuterMeasure] using key
  · intro h
    intro n X hX
    have hp := (EuclideanSpace.volume_preserving_measurableEquiv (Fin n)).symm
    have key := @h n ((EuclideanSpace.measurableEquiv (Fin n)).symm ⁻¹' X) (by
      intro ε hε
      obtain ⟨Y, hXY, hY⟩ := hX ε hε
      refine ⟨(EuclideanSpace.measurableEquiv (Fin n)).symm ⁻¹' Y, Set.preimage_mono hXY, ?_⟩
      simp only [Measure.coe_toOuterMeasure]
      rw [hp.measure_preimage_equiv]
      exact hY)
    simp only [Measure.coe_toOuterMeasure] at key
    rw [hp.measure_preimage_equiv] at key
    exact key
