-- R's statement differs from P's only by a `let mStar := volume.toOuterMeasure` binder,
-- which is definitionally (zeta) equal to P's inlined `volume.toOuterMeasure`.
theorem cert : (type_of% @R.lebesgue_outer_measure_union_le) ↔
    (type_of% @P.jirilebl_ra_ch_multivar_int_2077) := by
  constructor
  · intro h
    intro n A B
    exact h n A B
  · intro h
    intro n A B
    exact h n A B
