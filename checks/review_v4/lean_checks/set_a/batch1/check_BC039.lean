import Mathlib

-- The agent's statement is discharged by the existing Mathlib instance; it says nothing about
-- the operation or about closure of {det = 1} under multiplication/inverses.
theorem sl_isGroup (n : ℕ) :
    ∃ _inst : Group (Matrix.SpecialLinearGroup (Fin n) ℝ), True := ⟨inferInstance, trivial⟩

-- Same pattern is provable for a type with a nonsensical operation choice, e.g. any group structure on ℕ
example : ∃ _inst : Group (Multiplicative (ZMod 3)), True := ⟨inferInstance, trivial⟩
