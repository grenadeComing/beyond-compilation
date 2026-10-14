import Mathlib

-- `≃*` uses the ring multiplication of `ZMod 2`, a monoid with absorbing 0, not a group.
-- So the agent's statement for BC058 is false.
example : ¬ (∃ G : Type, ∃ _inst : Group G, Nonempty (G ≃* ZMod 2)) := by
  rintro ⟨G, _, ⟨e⟩⟩
  have h1 : e.symm 0 * e.symm 0 = e.symm 0 := by
    rw [← map_mul]; simp
  have h2 : e.symm 0 = 1 := by simpa using h1
  have h3 := congrArg e h2
  simp at h3
