import Mathlib

/-- The agent's statement is true and provable from the hom properties. -/
theorem BC090_agent (θ θ₁ θ₂ : Real.Angle) :
    rotation (Real.Angle.toCircle θ₁) * rotation (Real.Angle.toCircle θ₂) =
        rotation (Real.Angle.toCircle (θ₁ + θ₂)) ∧
      (rotation (Real.Angle.toCircle θ))⁻¹ = rotation (Real.Angle.toCircle (-θ)) ∧
        rotation (Real.Angle.toCircle θ₁) * rotation (Real.Angle.toCircle θ₂) =
          rotation (Real.Angle.toCircle θ₂) * rotation (Real.Angle.toCircle θ₁) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.Angle.toCircle_add, map_mul]
  · rw [Real.Angle.toCircle_neg, map_inv]
  · rw [← map_mul, ← map_mul, mul_comm]

/-- Real-angle version: rho_theta := rotation (toCircle ↑θ) acts on ℂ ≅ ℝ² as z ↦ e^{iθ} z,
and the coercion ℝ → Real.Angle is a surjective additive hom, so the ℝ-indexed claims
are instances of the agent's statement. -/
example (θ : ℝ) (z : ℂ) :
    rotation (Real.Angle.toCircle (θ : Real.Angle)) z = Complex.exp (θ * Complex.I) * z := by
  simp [rotation_apply, Real.Angle.toCircle_coe]

example (θ₁ θ₂ : ℝ) :
    rotation (Real.Angle.toCircle ((θ₁ : Real.Angle))) * rotation (Real.Angle.toCircle (θ₂ : Real.Angle)) =
      rotation (Real.Angle.toCircle (((θ₁ + θ₂ : ℝ)) : Real.Angle)) := by
  rw [Real.Angle.coe_add]; exact (BC090_agent 0 θ₁ θ₂).1

example (θ : ℝ) :
    (rotation (Real.Angle.toCircle (θ : Real.Angle)))⁻¹ =
      rotation (Real.Angle.toCircle ((-θ : ℝ) : Real.Angle)) := by
  rw [Real.Angle.coe_neg]; exact (BC090_agent θ 0 0).2.1

example : Function.Surjective ((↑) : ℝ → Real.Angle) := QuotientAddGroup.mk_surjective

#print axioms BC090_agent
