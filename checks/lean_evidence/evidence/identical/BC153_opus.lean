-- P writes `volume.toOuterMeasure Y` where R writes `volume Y`; in Mathlib the coercion of a
-- measure to a function is `μ.toOuterMeasure` (`Measure.coe_toOuterMeasure` is `rfl`),
-- so the two statements are definitionally the same up to binder explicitness.
theorem cert : (type_of% @R.outer_measure_zero_of_small_supersets) ↔
    (type_of% @P.outer_measure_zero_of_arbitrarily_small_supersets) := by
  constructor
  · intro h n X hX
    exact h n X hX
  · intro h n X hX
    exact h X hX
