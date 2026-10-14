import Mathlib

#print IsCoveringMap
#print IsEvenlyCovered
#check @IsCoveringMap.isOpenMap
#check (Circle : Type)
#print Circle

-- A non-surjective covering map: the inclusion of ℝ into ℝ ⊕ Unit.
example : ¬ Function.Surjective (Sum.inl : ℝ → ℝ ⊕ Unit) := by
  intro h
  obtain ⟨x, hx⟩ := h (Sum.inr ())
  cases hx
