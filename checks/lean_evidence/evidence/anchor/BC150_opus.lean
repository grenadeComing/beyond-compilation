-- Differences: (1) P has an extra hypothesis `a < b`, implied by `c ∈ Ioo a b`;
-- (2) R states differentiability on (a,b)\{c} pointwise as `DifferentiableAt`, P as
-- `DifferentiableOn ℝ f (Ioo a b \ {c})`; these agree because (a,b)\{c} is open.
-- The limit hypothesis and the conclusion are identical.
theorem cert : (type_of% @R.deriv_at_point_of_limit_of_deriv) ↔
    (type_of% @P.jirilebl_ra_ch_der_1129) := by
  constructor
  · intro h
    intro a b c L _hab hc f hcont hdiff hlim
    refine h a b c L f hc hcont ?_ hlim
    intro x hx hxc
    have hopen : IsOpen (Set.Ioo a b \ {c}) := isOpen_Ioo.sdiff isClosed_singleton
    have hmem : x ∈ Set.Ioo a b \ {c} := ⟨hx, hxc⟩
    exact hdiff.differentiableAt (hopen.mem_nhds hmem)
  · intro h
    intro a b c L f hc hcont hdiff hlim
    refine h (hc.1.trans hc.2) hc hcont ?_ hlim
    intro x hx
    exact (hdiff x hx.1 hx.2).differentiableWithinAt
