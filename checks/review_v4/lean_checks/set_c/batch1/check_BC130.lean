import Mathlib

-- For real sequences, Summable ↔ Summable of absolute values
example (f : ℕ → ℝ) : Summable (fun n => |f n|) ↔ Summable f := summable_abs_iff

-- Hence the gpt52 hypotheses are contradictory
example {a : ℕ → ℝ} (h : Summable fun n : ℕ => a (n + 1))
    (habs : ¬ Summable fun n : ℕ => |a (n + 1)|) : False :=
  habs (summable_abs_iff.mpr h)

-- the alternating harmonic series (conditionally convergent) is NOT Summable in Mathlib
example : ¬ Summable (fun n : ℕ => (-1 : ℝ) ^ n / (n + 1)) := by
  intro h
  have := summable_abs_iff.mpr h
  have h2 : (fun n : ℕ => |(-1 : ℝ) ^ n / (n + 1)|) = fun n : ℕ => 1 / ((n:ℝ) + 1) := by
    funext n
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow]
    congr 1
    exact abs_of_pos (by positivity)
  rw [h2] at this
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp (by simpa [Nat.cast_add, Nat.cast_one] using this))
