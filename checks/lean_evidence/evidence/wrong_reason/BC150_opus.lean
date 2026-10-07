/-! Judge claim: `Tendsto (deriv f) (nhdsWithin c {c}ᶜ) (nhds L)` is a strictly stronger hypothesis
than the limit taken within (a,b) \ {c}. Since c is an interior point of (a,b), the two
filters coincide, so the hypotheses are equivalent. -/

theorem claim_punctured_nhds_eq_within_domain (a b c : ℝ) (hc : c ∈ Set.Ioo a b) :
    nhdsWithin c {c}ᶜ = nhdsWithin c (Set.Ioo a b \ {c}) := by
  rw [Set.diff_eq, nhdsWithin_inter_of_mem]
  exact mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hc.1 hc.2)

theorem claim_hlim_iff_limit_within_domain (a b c L : ℝ) (f : ℝ → ℝ) (hc : c ∈ Set.Ioo a b) :
    Filter.Tendsto (deriv f) (nhdsWithin c {c}ᶜ) (nhds L) ↔
      Filter.Tendsto (deriv f) (nhdsWithin c (Set.Ioo a b \ {c})) (nhds L) := by
  rw [claim_punctured_nhds_eq_within_domain a b c hc]
