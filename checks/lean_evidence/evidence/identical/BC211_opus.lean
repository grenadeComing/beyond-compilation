-- Same statement: R has x₀ x₁ explicit and proves continuity of `F (0, ·)` / `F (1, ·)`
-- with `fun_prop`, P has them implicit and gives explicit continuity terms; the continuity
-- proofs are irrelevant (proof irrelevance).
theorem cert.{u, v} : (type_of% @R.homotopy_fundamentalGroup_naturality.{u, v}) ↔
    (type_of% @P.homotopy_induced_fundamental_group_naturality.{u, v}) := by
  constructor
  · intro h X Y _ _ F x₀ x₁ x y hy γ
    exact h F x₀ x₁ x y hy γ
  · intro h X Y _ _ F x₀ x₁ x y hy γ
    exact h F x y hy γ
