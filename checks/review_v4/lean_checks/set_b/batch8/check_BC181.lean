import Mathlib
open Set Filter TopologicalSpace
open scoped Topology

-- Herald's statement, universally quantified, is false: X = ℝ (T2), Y = Bool with the indiscrete topology (⊤).
example : ¬ (∀ (f g : ℝ → Bool), @Dense ℝ _ {x | f x = g x} →
    @Continuous ℝ Bool _ (⊤ : TopologicalSpace Bool) f →
    @Continuous ℝ Bool _ (⊤ : TopologicalSpace Bool) g → f = g) := by
  intro h
  have key := h (fun _ => false) (fun x => decide (x = 0)) ?_ ?_ ?_
  · have := congrFun key 0
    simp at this
  · have : {x : ℝ | (fun _ => false) x = (fun x => decide (x = 0)) x} = {(0:ℝ)}ᶜ := by
      ext x; simp [eq_comm]
    rw [this]
    exact dense_compl_singleton 0
  · exact @continuous_top ℝ Bool _ _
  · exact @continuous_top ℝ Bool _ _
