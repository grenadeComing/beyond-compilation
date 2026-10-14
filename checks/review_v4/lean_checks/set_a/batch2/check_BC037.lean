import Mathlib

/-- The agent's conclusion holds for every matrix, without using nonsingularity:
the closure of the set of all matrices contains every matrix. -/
theorem BC037_agent_trivial {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    A ∈ Subsemigroup.closure ({E : Matrix n n ℝ | True} : Set (Matrix n n ℝ)) :=
  Subsemigroup.subset_closure trivial

#print axioms BC037_agent_trivial
