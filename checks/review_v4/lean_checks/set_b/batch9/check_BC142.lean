import Mathlib

-- stepfun statement is false: take c = 0, a = 0, I = {0}, f = id.
-- f agrees with the (zero) series on I, DifferentiableOn on a singleton holds,
-- but deriv f 0 = 1 ≠ 0 = ∑' of the differentiated (zero) series.
example : ¬ (∀ (c : ℕ → ℝ) (a : ℝ) (rho : ℝ) (hrho : rho > 0) (I : Set ℝ) (f : ℝ → ℝ)
    (hf : ∀ x ∈ I, f x = ∑' n : ℕ, c n * (x - a) ^ n)
    (h : ∀ x ∈ I, Summable (fun n => c n * (x - a) ^ n)),
    DifferentiableOn ℝ f I ∧
    ∀ x ∈ I, deriv f x = ∑' n : ℕ, (n + 1) * c (n + 1) * (x - a) ^ n ∧
    (∀ x ∈ I, Summable (fun n => (n + 1) * c (n + 1) * (x - a) ^ n))) := by
  intro H
  have := H (fun _ => 0) 0 1 one_pos {0} id (by simp) (by simp [summable_zero])
  have h2 := (this.2 0 rfl).1
  simp at h2
