import Mathlib

open Set Function

-- herald's hypotheses on the singleton {p} hold for every function f.
example (f : ℂ → ℂ) (p : ℂ) : DifferentiableOn ℂ f {p} := differentiableOn_singleton
example (f : ℂ → ℂ) (p : ℂ) : ContinuousOn (deriv f) {p} := continuousOn_singleton _ _

-- The W-part of the conclusion is trivial with W = univ; Injective (MapsTo.restrict ..) is just InjOn.
example (f : ℂ → ℂ) (V : Set ℂ) (h : InjOn f V) :
    IsOpen (univ : Set ℂ) ∧ MapsTo f V univ ∧ Injective (MapsTo.restrict f V univ (mapsTo_univ f V)) :=
  ⟨isOpen_univ, mapsTo_univ f V, (MapsTo.restrict_inj (mapsTo_univ f V)).mpr h⟩
