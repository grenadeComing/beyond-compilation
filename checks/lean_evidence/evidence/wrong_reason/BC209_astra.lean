/-! Decisive judge claim: the output "does not state that p is a *universal* covering map (it only
concludes `IsCoveringMap p`; universality would require an explicit `IsUniversalCover`-type
statement)". This is about the definition of "universal cover" (a covering map whose total space is
simply connected; `Y` is assumed `SimplyConnectedSpace`), and Mathlib has no universal-cover
predicate, so it is not checked here.
Secondary judge claim: `hcovering` "is only a disjointness-of-translates neighborhood condition
rather than a standard covering action / free action". Checked below: `hcovering` is equivalent to
the textbook (Hatcher) covering-space-action condition "all translates gU are pairwise
disjoint", and it implies that the action is free. -/

theorem claim_hcovering_iff_translates_pairwise_disjoint
    {Γ Y : Type*} [Group Γ] [TopologicalSpace Y] [MulAction Γ Y] :
    (∀ y : Y, ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧
      ∀ γ : Γ, γ ≠ 1 → Disjoint U ((fun z : Y => γ • z) '' U)) ↔
    (∀ y : Y, ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧
      ∀ g h : Γ, g ≠ h → Disjoint ((fun z : Y => g • z) '' U) ((fun z : Y => h • z) '' U)) := by
  constructor
  · intro H y
    obtain ⟨U, hUo, hyU, hd⟩ := H y
    refine ⟨U, hUo, hyU, fun g h hgh => ?_⟩
    rw [Set.disjoint_left]
    rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, hvu⟩
    have hvu' : h • v = g • u := hvu
    have hne : g⁻¹ * h ≠ 1 := by
      intro h1
      exact hgh (inv_mul_eq_one.mp h1)
    have hmem : u ∈ (fun z : Y => (g⁻¹ * h) • z) '' U := by
      refine ⟨v, hv, ?_⟩
      show (g⁻¹ * h) • v = u
      rw [mul_smul, hvu', inv_smul_smul]
    exact Set.disjoint_left.mp (hd _ hne) hu hmem
  · intro H y
    obtain ⟨U, hUo, hyU, hd⟩ := H y
    refine ⟨U, hUo, hyU, fun γ hγ => ?_⟩
    have := (hd γ 1 hγ).symm
    simpa [one_smul] using this

theorem claim_hcovering_implies_free
    {Γ Y : Type*} [Group Γ] [TopologicalSpace Y] [MulAction Γ Y]
    (hcovering : ∀ y : Y, ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧
      ∀ γ : Γ, γ ≠ 1 → Disjoint U ((fun z : Y => γ • z) '' U)) :
    ∀ (γ : Γ) (y : Y), γ • y = y → γ = 1 := by
  intro γ y hγy
  by_contra hγ
  obtain ⟨U, -, hyU, hd⟩ := hcovering y
  exact Set.disjoint_left.mp (hd γ hγ) hyU ⟨y, hyU, hγy⟩
