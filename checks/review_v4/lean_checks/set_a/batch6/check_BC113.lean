import Mathlib

open Function

-- What RightInvOn g f V means
example (f g : ℂ → ℂ) (V : Set ℂ) : Set.RightInvOn g f V ↔ ∀ y ∈ V, f (g y) = y := Iff.rfl

-- Counterexample: f = exp, U = univ, p = 0. The agent's conclusion is false.
example :
    ¬ ∃ V W : Set ℂ,
      IsOpen V ∧ IsOpen W ∧ (0:ℂ) ∈ V ∧ V ⊆ Set.univ ∧ Complex.exp '' V = W ∧ Set.InjOn Complex.exp V ∧
        ∃ g : ℂ → ℂ,
          DifferentiableOn ℂ g W ∧ Set.LeftInvOn g Complex.exp V ∧ Set.RightInvOn g Complex.exp V := by
  rintro ⟨V, W, -, -, h0, -, -, -, g, -, -, hR⟩
  have := hR h0
  exact Complex.exp_ne_zero _ this

-- hypotheses of the agent theorem hold for exp at p = 0
example : IsOpen (Set.univ : Set ℂ) ∧ DifferentiableOn ℂ Complex.exp Set.univ ∧ deriv Complex.exp 0 ≠ 0 := by
  refine ⟨isOpen_univ, Complex.differentiable_exp.differentiableOn, ?_⟩
  simp [Complex.deriv_exp]
