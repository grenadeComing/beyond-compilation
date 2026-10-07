-- R: (n s) (hconv) (hbdd) ⊢ IsBounded s ∧ volume (frontier s) = 0
-- P: {n s} (hbounded) (hconvex) ⊢ P.IsJordanMeasurableSet s, which unfolds to the same conjunction.
-- Only binder explicitness and hypothesis order differ.
theorem cert : (type_of% @R.bounded_convex_jordan_measurable) ↔
    (type_of% @P.bounded_convex_isJordanMeasurableSet) := by
  constructor
  · intro h n s hb hc
    exact h n s hc hb
  · intro h n s hc hb
    exact h hb hc
