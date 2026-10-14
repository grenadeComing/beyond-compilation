import Mathlib

-- The agent's statement is proved by the trivial homomorphism; δ plays no role.
example (G : Type*) [Group G] (n : ℕ) (F : Type*) [Field F]
    (δ : G →* Equiv.Perm (Fin n)) :
    ∃ ρ : G →* Matrix.GeneralLinearGroup (Fin n) F, True := ⟨1, trivial⟩

-- Convention check: Mathlib's permMatrix is anti-multiplicative.
open Equiv in
example (σ τ : Perm (Fin 3)) :
    (σ * τ).permMatrix ℚ = τ.permMatrix ℚ * σ.permMatrix ℚ := by
  simp only [Equiv.Perm.permMatrix, Equiv.Perm.mul_def, Equiv.toPEquiv_trans, PEquiv.toMatrix_trans]
