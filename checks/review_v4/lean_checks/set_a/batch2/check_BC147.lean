import Mathlib

/-- With the vacuous harmonicity placeholder, the agent's statement is false:
U = univ, f(x,y) = -x^2 has a maximum at (0,0) but is not constant. -/
theorem BC147_false :
    ¬ (∀ {U : Set (ℝ × ℝ)}, IsOpen U → IsConnected U → ∀ {f : ℝ × ℝ → ℝ},
      (∀ x ∈ U, True) → ∀ {p : ℝ × ℝ}, p ∈ U → (∀ x ∈ U, f x ≤ f p) → ∀ x ∈ U, f x = f p) := by
  intro h
  have := @h Set.univ isOpen_univ isConnected_univ (fun x => -(x.1 ^ 2)) (fun _ _ => trivial)
    (0, 0) (Set.mem_univ _)
    (fun x _ => by show -(x.1 ^ 2) ≤ -((0:ℝ) ^ 2); nlinarith [sq_nonneg x.1])
    (1, 0) (Set.mem_univ _)
  norm_num at this

#print axioms BC147_false
