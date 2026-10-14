import Mathlib

open Complex

-- How does `DifferentiableAt ℝ ψ z` elaborate for ψ : ℂ → ℝ → ℂ ?
set_option pp.explicit true in
example (ψ : ℂ → ℝ → ℂ) (z : ℂ) : DifferentiableAt ℝ ψ z ↔ DifferentiableAt ℝ ψ z := Iff.rfl

#synth TopologicalSpace (ℝ → ℂ)
#synth AddCommGroup (ℝ → ℂ)
#synth Module ℝ (ℝ → ℂ)
#check @DifferentiableAt

-- Counterexample candidate: ψ z t = conj z is continuous and ℝ-differentiable (as a map into ℝ → ℂ),
-- but ∫_0^1 conj z dt = conj z is not ℂ-differentiable.
example : Continuous (fun (z : ℂ) (_t : ℝ) => (starRingEnd ℂ) z) :=
  continuous_pi fun _ => Complex.continuous_conj

-- ψ = (const map) ∘ conjCLE is a continuous ℝ-linear map, hence ℝ-differentiable everywhere
example (z : ℂ) : DifferentiableAt ℝ (fun (z : ℂ) (_t : ℝ) => (starRingEnd ℂ) z) z := by
  let L : ℂ →L[ℝ] (ℝ → ℂ) := ContinuousLinearMap.pi (fun _ : ℝ => (Complex.conjCLE : ℂ →L[ℝ] ℂ))
  have : (fun (z : ℂ) (_t : ℝ) => (starRingEnd ℂ) z) = L := by
    funext z t; rfl
  rw [this]
  refine ⟨L, ?_⟩
  constructor
  simp only [map_sub, sub_self]
  first
  | exact Asymptotics.IsLittleOTVS.zero _ _
  | exact Asymptotics.isLittleOTVS_zero
  | exact (Asymptotics.isLittleOTVS_zero).2 trivial
  | exact?

#print HasFDerivAtFilter

-- the integral is conj z
example (z : ℂ) : (∫ t in (0:ℝ)..1, (fun (z : ℂ) (_t : ℝ) => (starRingEnd ℂ) z) z t) = (starRingEnd ℂ) z := by
  simp
