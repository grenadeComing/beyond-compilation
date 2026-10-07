-- R takes the covering map as a bundled `f : C(X, Y)`, P as an unbundled `f : X → Y`
-- (continuity then comes from `hf.continuous`). Path.map's continuity argument is a proof,
-- so the two image paths agree by proof irrelevance.
theorem cert.{u, v} : (type_of% @R.coveringMap_induced_fundamentalGroup_injective.{u, v}) ↔
    (type_of% @P.covering_map_fundamentalGroup_injective.{u, v}) := by
  constructor
  · intro h X Y _ _ _ f hf x γ γ' hγ
    exact h ⟨f, hf.continuous⟩ hf x γ γ' hγ
  · intro h X Y _ _ _ f hf x p q hpq
    exact h hf x p q hpq
