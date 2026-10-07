-- NOT EQUIVALENT. The rejected output R (with `[Nonempty X] [Nonempty Y]`) is true; the anchor P
-- (no nonemptiness) is false: X = Empty, Y = ℝ gives X × Y empty, hence compact, while ℝ is not
-- compact. Hence `R ↔ P` is refutable and no `cert` can exist; we prove its negation instead.
universe u v

theorem R_true : (type_of% @R.compact_and_compact_iff_prod_compact.{u, v}) := by
  intro X Y _ _ _ _
  constructor
  · rintro ⟨hX, hY⟩
    infer_instance
  · intro hXY
    constructor
    · have hX := isCompact_range (continuous_fst : Continuous (Prod.fst : X × Y → X))
      rw [(Prod.fst_surjective : Function.Surjective (Prod.fst : X × Y → X)).range_eq] at hX
      exact isCompact_univ_iff.mp hX
    · have hY := isCompact_range (continuous_snd : Continuous (Prod.snd : X × Y → Y))
      rw [(Prod.snd_surjective : Function.Surjective (Prod.snd : X × Y → Y)).range_eq] at hY
      exact isCompact_univ_iff.mp hY

theorem P_false : ¬ (type_of% @P.benmckay_top_topology_495.{0, 0}) := by
  intro h
  have hc : CompactSpace (Empty × ℝ) :=
    ⟨by rw [Set.univ_eq_empty_iff.mpr (inferInstance : IsEmpty (Empty × ℝ))]; exact isCompact_empty⟩
  have hR : CompactSpace ℝ := ((h Empty ℝ).2 hc).2
  exact not_compactSpace_iff.mpr inferInstance hR

theorem not_cert : ¬ ((type_of% @R.compact_and_compact_iff_prod_compact.{0, 0}) ↔
    (type_of% @P.benmckay_top_topology_495.{0, 0})) :=
  fun h => P_false (h.1 R_true)

#print axioms not_cert
