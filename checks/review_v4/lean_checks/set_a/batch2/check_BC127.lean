import Mathlib

open MeasureTheory

/-- The agent's statement (all disjoint open sets, no rectangle structure) is true:
it follows directly from countable additivity on measurable sets, so it is a strict
generalization of the rectangle claim. -/
theorem BC127_agent_true
    (n N : ℕ) (R : Fin N → Set (EuclideanSpace ℝ (Fin n)))
    (hopen : ∀ k, IsOpen (R k))
    (hdisj : Pairwise fun i j => Disjoint (R i) (R j)) :
    (Measure.toOuterMeasure (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))))
        (⋃ k, R k) =
      ∑ k, (Measure.toOuterMeasure (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n)))) (R k) := by
  simp only [Measure.coe_toOuterMeasure]
  rw [measure_iUnion hdisj (fun k => (hopen k).measurableSet), tsum_fintype]

#print axioms BC127_agent_true
