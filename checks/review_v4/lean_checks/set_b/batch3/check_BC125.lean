import Mathlib

-- goedel_prover's statement is false for X = ℝ (complete), s = univ (open, closed, nonempty, not compact)
example : ¬ (∀ (s : Set ℝ), IsOpen s → IsClosed s → s.Nonempty → IsCompact s) := by
  intro h
  have := h Set.univ isOpen_univ isClosed_univ Set.univ_nonempty
  exact noncompact_univ ℝ this
