/-! Decisive judge claim: the output "only asserts `IsCoveringMap`, not a universal covering property
(e.g. `IsUniversalCover`)". This is about the definition of "universal cover" (a covering map whose
total space is simply connected; `Y` is assumed `SimplyConnectedSpace`), and Mathlib has no
universal-cover predicate, so it is not checked here.
Secondary judge claim: "the Lean hypotheses encode a local-disjointness condition but do not
explicitly require freeness, so the match of hypotheses is not exact". Checked below: `hcov` implies
freeness, and `hcov` is equivalent to the textbook (Hatcher) condition "all translates gU are
pairwise disjoint". -/

theorem claim_hcov_implies_free
    {Γ Y : Type*} [Group Γ] [TopologicalSpace Y] [MulAction Γ Y]
    (hcov : ∀ y : Y, ∃ U ∈ nhds y, ∀ g : Γ, g ≠ 1 →
      (fun z : Y => g • z) '' U ∩ U = ∅) :
    ∀ (g : Γ) (y : Y), g • y = y → g = 1 := by
  intro g y hgy
  by_contra hg
  obtain ⟨U, hU, hd⟩ := hcov y
  have hy : y ∈ U := mem_of_mem_nhds hU
  have hmem : y ∈ (fun z : Y => g • z) '' U ∩ U := ⟨⟨y, hy, hgy⟩, hy⟩
  rw [hd g hg] at hmem
  exact hmem

theorem claim_hcov_iff_translates_pairwise_disjoint
    {Γ Y : Type*} [Group Γ] [TopologicalSpace Y] [MulAction Γ Y] :
    (∀ y : Y, ∃ U ∈ nhds y, ∀ g : Γ, g ≠ 1 →
      (fun z : Y => g • z) '' U ∩ U = ∅) ↔
    (∀ y : Y, ∃ U ∈ nhds y, ∀ g h : Γ, g ≠ h →
      Disjoint ((fun z : Y => g • z) '' U) ((fun z : Y => h • z) '' U)) := by
  constructor
  · intro H y
    obtain ⟨U, hU, hd⟩ := H y
    refine ⟨U, hU, fun g h hgh => ?_⟩
    rw [Set.disjoint_left]
    rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, hvu⟩
    have hvu' : h • v = g • u := hvu
    have hne : g⁻¹ * h ≠ 1 := by
      intro h1
      exact hgh (inv_mul_eq_one.mp h1)
    have hmem : u ∈ (fun z : Y => (g⁻¹ * h) • z) '' U ∩ U := by
      refine ⟨⟨v, hv, ?_⟩, hu⟩
      show (g⁻¹ * h) • v = u
      rw [mul_smul, hvu', inv_smul_smul]
    rw [hd _ hne] at hmem
    exact hmem
  · intro H y
    obtain ⟨U, hU, hd⟩ := H y
    refine ⟨U, hU, fun g hg => ?_⟩
    have := hd g 1 hg
    rw [← Set.disjoint_iff_inter_eq_empty]
    simpa [one_smul] using this
