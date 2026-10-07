-- The two statements differ only in the order of the instance arguments
-- `[T2Space X]` / `[TopologicalSpace Y]` and in the name of the dense set.
-- (Both put the Hausdorff assumption on the domain X, exactly as the NL statement does.)
theorem cert.{u, v} : (type_of% @R.continuous_maps_eq_of_agree_on_dense.{u, v}) ↔
    (type_of% @P.eq_of_agree_on_dense.{u, v}) := by
  constructor
  · intro h X Y _ _ _ f g hf hg S hS hfg
    exact h f g hf hg S hS hfg
  · intro h X Y _ _ _ f g hf hg S hS hfg
    exact h f g hf hg S hS hfg
