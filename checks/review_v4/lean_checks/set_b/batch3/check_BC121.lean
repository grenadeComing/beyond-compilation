import Mathlib
open Filter Topology

-- herald: hypothesis h holds in every topological space (take V = U)
example {α : Type*} [MetricSpace α] :
    ∀ (U : Set α), IsOpen U → ∀ x ∈ U, ∃ V ∈ 𝓝 x, V ⊆ U :=
  fun U hU x hx => ⟨U, hU.mem_nhds hx, le_rfl⟩

-- herald: conclusion false even in a compact metric space (Bool, alternating sequence)
example : ¬ (∀ (u : ℕ → Bool), ∃ a, Tendsto u atTop (𝓝 a)) := by
  intro h
  obtain ⟨a, ha⟩ := h (fun n => decide (Even n))
  rw [nhds_discrete, tendsto_pure] at ha
  obtain ⟨N, hN⟩ := eventually_atTop.mp ha
  have h1 := hN (2*N) (by omega)
  have h2 := hN (2*N+1) (by omega)
  simp at h1 h2
  rw [h1] at h2
  exact Bool.noConfusion h2

-- stepfun: conclusion trivially true with y = x, N = 1 (no compactness used)
example {X : Type*} [MetricSpace X] (x : ℕ → X) :
    ∃ y : ℕ → X, (∃ N : ℕ, ∀ n : ℕ, N ≤ n → dist (x n) (y n) < 1 / n) := by
  refine ⟨x, 1, fun n hn => ?_⟩
  simp only [dist_self]
  have : (0:ℝ) < n := by exact_mod_cast hn
  positivity
