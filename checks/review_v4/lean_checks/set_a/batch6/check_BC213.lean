import Mathlib

-- Condition (2) of the agent's statement is trivially true for every Z and g.
example (Z : Set ℂ) (g : ℂ → ℂ) :
    ∀ x : ↥Z, ∀ γ : Path x x,
      ∃ γ0 : Path (g (x : ℂ)) (g (x : ℂ)), Path.Homotopic γ0 (Path.refl _) :=
  fun x _ => ⟨Path.refl _, Path.Homotopic.refl _⟩

-- Hence the agent's RHS is equivalent to "g has no zeros on Z".
example (Z : Set ℂ) (g : ℂ → ℂ) :
    ((∀ z ∈ Z, g z ≠ 0) ∧
        ∀ x : ↥Z, ∀ γ : Path x x,
            ∃ γ0 : Path (g (x : ℂ)) (g (x : ℂ)), Path.Homotopic γ0 (Path.refl _))
      ↔ (∀ z ∈ Z, g z ≠ 0) :=
  ⟨fun h => h.1, fun h => ⟨h, fun x _ => ⟨Path.refl _, Path.Homotopic.refl _⟩⟩⟩

-- BoxIntegral boxes are non-degenerate (relevant to BC135)
#check @BoxIntegral.Box.lower_lt_upper
