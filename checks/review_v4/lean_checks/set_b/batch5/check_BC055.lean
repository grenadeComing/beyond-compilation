import Mathlib

-- Which Inv instance is used for Matrix (Fin 2) (Fin 2) F?
example {F : Type*} [Field F] (M : Matrix (Fin 2) (Fin 2) F) : M⁻¹ = Ring.inverse M.det • M.adjugate := Matrix.inv_def M

-- The stepfun statement is provable, i.e. ⁻¹ is the genuine matrix inverse here.
theorem srdoty_alg_linear_gps_838 {F : Type*} [Field F] (E : F → Matrix (Fin 2) (Fin 2) F)
    (hE : ∀ t, E t = !![1, t; 0, 1]) :
    ∀ t, (E t)⁻¹ = E (-t) := by
  intro t
  rw [hE, hE]
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

-- Entrywise inverse would give a different matrix: e.g. the (0,1) entry would be t⁻¹, not -t.
