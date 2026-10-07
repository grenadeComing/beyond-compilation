-- The rejected output and the anchor are textually identical statements.
universe u

theorem cert : (type_of% @R.contractible_connected_and_trivial_homotopyGroups.{u}) ↔
    (type_of% @P.contractible_connected_and_trivial_homotopyGroups.{u}) := by
  constructor
  · intro h
    exact h
  · intro h
    exact h
