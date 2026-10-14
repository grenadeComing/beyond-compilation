import Mathlib

-- The gpt52 statement is closed by the structure field: hypothesis type already contains continuity
theorem linear_bounded_isContinuous
    {𝕜 : Type*} [NormedField 𝕜]
    {X : Type*} [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type*} [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (A : X →L[𝕜] Y) : Continuous A := A.cont

-- A non-vacuous version over ℝ: linear map + bound implies continuity
example {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : X →ₗ[ℝ] Y) (hA : ∃ C, ∀ x, ‖A x‖ ≤ C * ‖x‖) : Continuous A := by
  obtain ⟨C, hC⟩ := hA
  exact AddMonoidHomClass.continuous_of_bound A C hC
