import Mathlib

/-- The agent's statement is exactly the general-topology lemma `continuous_iff_continuousAt`,
valid for arbitrary topological spaces; the Euclidean / epsilon-delta content is absent. -/
theorem BC197_agent_is_general {n m : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {Y : Set (EuclideanSpace ℝ (Fin m))} (f : X → Y) :
    Continuous f ↔ ∀ x : X, ContinuousAt f x := continuous_iff_continuousAt

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ x, ContinuousAt f x := continuous_iff_continuousAt

/-- The epsilon-delta link is a separate metric-space lemma. -/
example {n m : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {Y : Set (EuclideanSpace ℝ (Fin m))} (f : X → Y) (x : X) :
    ContinuousAt f x ↔ ∀ ε > 0, ∃ δ > 0, ∀ {y : X}, dist y x < δ → dist (f y) (f x) < ε :=
  Metric.continuousAt_iff

#print axioms BC197_agent_is_general
