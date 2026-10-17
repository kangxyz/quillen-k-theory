# Complexes of modules

These local candidates retain the original complexes, linear maps, chosen bounds
and chain homotopies. `FiniteParametrix`, the two `LinearMapCone` files, `SplitPivot`,
and the finite-domination files give actual finite-projective replacements and
their signed degree coordinates. `ProjectiveStabilization` constructs the stated
finite-free model of a complex plus its shift; it does not remove the shifted
summand.

The `Principal` files clear map/differential/homotopy denominators for finitely
presented finite-support terms, descend finite-free models, and prove locality
and tail truncation on a generating principal cover. These results use arbitrary
commutative rings with the hypotheses stated in each interface.

`FiniteProjectiveHomology` controls highest homology under its actual bounds,
without claiming finiteness of all lower homology over noncoherent rings.
`ConcentratedPerfectHomology` gives the concentrated single model. The Laurent
files retain their original signed chart maps and actual model equivalences.
`FiniteProjectiveResolution` separately assumes a noetherian coefficient ring;
its admissible resolutions use the general exact-category resolution interface,
with projective-dimension bounds or the stated PID specialization.
