import Mathlib

/-- The agent's statement is closed by `⟨_, rfl⟩`: it is an instance of the tautology
`∃ K, K = t`, and says nothing about the set intersection. -/
theorem BC045_agent_trivial {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    (G H : Subgroup (Matrix.GeneralLinearGroup n R)) :
    ∃ K : Subgroup (Matrix.GeneralLinearGroup n R), K = G ⊓ H := ⟨_, rfl⟩

example {α : Sort*} (t : α) : ∃ K : α, K = t := ⟨t, rfl⟩

#print axioms BC045_agent_trivial
