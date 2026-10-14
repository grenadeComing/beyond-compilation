import Mathlib

-- Conventions deciding the case: non-summable tsum is 0, non-multipliable tprod is 1,
-- and HasProd allows the limit 0.
#check @tsum_eq_zero_of_not_summable
#check @tprod_eq_one_of_not_multipliable
#print HasProd

/-- On the unit circle the partition series is never summable (terms have norm p(n) ≥ 1),
so the agent's LHS is 0 there; the RHS is 1 whenever the product is not multipliable. -/
example (x : ℂ) (hx : ‖x‖ = 1) :
    ¬ Summable (fun n : ℕ => (Fintype.card (Nat.Partition n) : ℂ) * x ^ n) := by
  intro hs
  have h0 := hs.tendsto_atTop_zero
  have hpos : ∀ n : ℕ, 1 ≤ ‖(Fintype.card (Nat.Partition n) : ℂ) * x ^ n‖ := by
    intro n
    rw [norm_mul, norm_pow, hx, one_pow, mul_one, Complex.norm_natCast]
    exact_mod_cast Fintype.card_pos
  have := (h0.norm).eventually (gt_mem_nhds (show ‖(0:ℂ)‖ < 1 by simp))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 this
  have := hN N le_rfl
  linarith [hpos N]
