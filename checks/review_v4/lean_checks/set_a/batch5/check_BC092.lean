import Mathlib

instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp [finrank_euclideanSpace]⟩

-- Aristotle's statement is exactly a Mathlib lemma about Mathlib's own rotation
theorem aristotle_708
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2))
    (θ : Real.Angle)
    (X : EuclideanSpace ℝ (Fin 2))
    (hX : X ≠ 0) :
    o.oangle X (o.rotation θ X) = θ := o.oangle_rotation_self_right hX θ

-- unoriented angle reading: angle X (R_θ X) = θ is false for θ = -π/2 (angle is ≥ 0)
example : ∀ (X Y : EuclideanSpace ℝ (Fin 2)), 0 ≤ InnerProductGeometry.angle X Y :=
  fun X Y => InnerProductGeometry.angle_nonneg X Y
example : ∀ (X Y : EuclideanSpace ℝ (Fin 2)), InnerProductGeometry.angle X Y ≤ Real.pi :=
  fun X Y => InnerProductGeometry.angle_le_pi X Y
