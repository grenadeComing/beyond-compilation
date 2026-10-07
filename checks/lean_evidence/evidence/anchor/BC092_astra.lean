-- NOT EQUIVALENT. The rejected output R is false, while the anchor P is true.
-- R uses `InnerProductGeometry.angle`, the unoriented angle with values in [0, π], and claims
-- it equals θ for every real θ; for θ = -1 (and X = e₀) the left side is ≥ 0 ≠ -1.
-- P uses the oriented angle `o.oangle` with θ : Real.Angle (ℝ mod 2π), which is Mathlib's
-- `Orientation.oangle_rotation_self_right`.
-- Hence `R ↔ P` is refutable and no `cert` can exist; we prove its negation instead.

theorem R_false : ¬ (type_of% @R.angle_eq_theta_of_rotation) := by
  intro h
  have h1 := h (-1) (EuclideanSpace.single 0 1) (by simp)
  have h2 : (0 : ℝ) ≤ -1 := h1 ▸ InnerProductGeometry.angle_nonneg _ _
  linarith

theorem P_true : (type_of% @P.srdoty_alg_linear_gps_708) := by
  intro o θ X hX
  exact o.oangle_rotation_self_right hX θ

theorem not_cert : ¬ ((type_of% @R.angle_eq_theta_of_rotation) ↔
    (type_of% @P.srdoty_alg_linear_gps_708)) :=
  fun h => R_false (h.2 P_true)

#print axioms not_cert
