-- NOT PROVED. The two statements are not related by a direct translation:
--  * R's `CoveringMapForUniversalProperty p` = continuous + SURJECTIVE + evenly covered by sheets;
--    Mathlib's `IsCoveringMap p` (used by P) does not require surjectivity (empty fibres allowed,
--    cf. `IsEvenlyCovered.of_preimage_eq_empty`).
--  * Hence R assumes the simply connected cover `q : U → Y` and the given cover `p : X → Y`
--    are surjective, while P does not (e.g. Y = two discrete points, U = one point satisfies
--    P's `hY` but no surjective simply connected cover of that Y exists);
--  * and R's right-hand side quantifies only over surjective coverings `r : Z → Y`, P's over all
--    coverings `q : Z → Y` (including non-surjective ones).
-- Relating them would need (i) CMUP ↔ IsCoveringMap ∧ Surjective (a Trivialization construction)
-- and (ii) lifting into non-surjective coverings from lifts into surjective ones, which is not
-- available without connectedness / local path-connectedness of X.
-- As closed propositions both appear to be false (Y = X = Warsaw circle, p = q = id: X is simply
-- connected, but its connected double cover admits no section, so no lift of p exists), which
-- would make them vacuously equivalent, but that is far beyond what can be checked here.
theorem cert.{u} : (type_of% @R.universal_covering_iff_unique_pointed_morphism.{u}) ↔
    (type_of% @P.universal_covering_iff_unique_morphism.{u}) := by
  constructor
  · intro h
    sorry
  · intro h
    sorry
