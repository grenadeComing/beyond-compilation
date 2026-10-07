-- R's E t is the matrix `fun i j => if i = j then 1 else if i = 0 then t else 0`, which is
-- entrywise equal to P's `!![1, t; 0, 1]`; `GL (Fin 2) F` is by definition `(Matrix ..)ˣ`,
-- and `{M | ∃ g ∈ H, ↑g = M}` is exactly the image `Units.val '' H`. Equation sides are swapped.
theorem cert.{u} : (type_of% @R.upper_unipotent_matrices_form_group.{u}) ↔
    (type_of% @P.upper_unitriangular_is_matrix_group.{u}) := by
  constructor
  · intro h F _
    have hfun : (fun t : F =>
        ((fun i j => if i = j then 1 else if i = 0 then t else 0 : Matrix (Fin 2) (Fin 2) F)))
        = (fun t : F => !![1, t; 0, 1]) := by
      funext t
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    obtain ⟨H, hH⟩ := h F
    refine ⟨H, ?_⟩
    rw [← hfun, hH]
    ext M
    simp
  · intro h F _
    have hfun : (fun t : F =>
        ((fun i j => if i = j then 1 else if i = 0 then t else 0 : Matrix (Fin 2) (Fin 2) F)))
        = (fun t : F => !![1, t; 0, 1]) := by
      funext t
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    obtain ⟨H, hH⟩ := h (F := F)
    intro E G
    have hE : E = fun t : F => !![1, t; 0, 1] := hfun
    refine ⟨H, ?_⟩
    show Set.range E = _
    rw [hE, ← hH]
    ext M
    simp
