import Mathlib

-- Aristotle's second conjunct is just `Fintype.card_pi` (no groups involved).
example (n : ℕ) (_ : 0 < n) :
    Fintype.card ((p : n.factorization.support) → Nat.Partition (n.factorization ↑p)) =
      ∏ p ∈ n.factorization.support, Fintype.card (Nat.Partition (n.factorization p)) := by
  rw [Fintype.card_pi]
  exact Finset.prod_coe_sort n.factorization.support (fun p => Fintype.card (Nat.Partition (n.factorization p)))

-- The agent's second conjunct is false at n = 4: p(4) = 5 but p(2) = 2.
example : Fintype.card (Nat.Partition 4) = 5 := by native_decide
example : Fintype.card (Nat.Partition 2) = 2 := by native_decide
-- hence the agent's conjunct is refuted at n = 4
example : ¬ (Fintype.card (Nat.Partition 4) =
    ∏ p ∈ (4:ℕ).primeFactors, Fintype.card (Nat.Partition ((4:ℕ).factorization p))) := by
  native_decide
