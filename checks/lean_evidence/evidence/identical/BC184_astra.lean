-- Hypothesis: R's "every open U ∋ x contains an open simply connected V ∋ x" is equivalent to
-- P's "the open simply connected neighbourhoods of x form a basis of 𝓝 x".
-- Conclusion: R additionally asks `PathConnectedSpace Y`, which is implied by
-- `SimplyConnectedSpace Y` (Mathlib instance); otherwise the conjuncts are permuted.
theorem cert.{u} : (type_of% @R.exists_universal_cover.{u}) ↔
    (type_of% @P.exists_universal_cover_of_locally_simply_connected.{u}) := by
  constructor
  · intro h X _ _ hloc
    have hlocal : ∀ (x : X) (U : Set X), IsOpen U → x ∈ U →
        ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ SimplyConnectedSpace V := by
      intro x U hU hxU
      obtain ⟨V, ⟨hVo, hxV, hV⟩, hVU⟩ := (hloc x).mem_iff.mp (hU.mem_nhds hxU)
      exact ⟨V, hVo, hxV, hVU, hV⟩
    obtain ⟨Y, tY, p, _, hsc, hsurj, hcov⟩ := h X hlocal
    exact ⟨Y, tY, p, hsc, hcov, hsurj⟩
  · intro h X _ _ hlocal
    have hloc : ∀ x : X, (nhds x).HasBasis
        (fun U : Set X => IsOpen U ∧ x ∈ U ∧ SimplyConnectedSpace U) id := by
      intro x
      refine ⟨fun t => ⟨fun ht => ?_, ?_⟩⟩
      · obtain ⟨U, hUt, hUo, hxU⟩ := mem_nhds_iff.mp ht
        obtain ⟨V, hVo, hxV, hVU, hV⟩ := hlocal x U hUo hxU
        exact ⟨V, ⟨hVo, hxV, hV⟩, hVU.trans hUt⟩
      · rintro ⟨U, ⟨hUo, hxU, _⟩, hUt⟩
        exact Filter.mem_of_superset (hUo.mem_nhds hxU) hUt
    obtain ⟨E, tE, p, hsc, hcov, hsurj⟩ := h hloc
    letI : TopologicalSpace E := tE
    exact ⟨E, tE, p, inferInstance, hsc, hsurj, hcov⟩
