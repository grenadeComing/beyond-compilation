-- The two statements are textually identical up to line breaks.
theorem cert.{u, v} : (type_of% @R.continuous_iff_closure_preimage_eq.{u, v}) ↔
    (type_of% @P.continuous_iff_closure_preimage_eq.{u, v}) := by
  constructor
  · intro h
    exact h
  · intro h
    exact h
