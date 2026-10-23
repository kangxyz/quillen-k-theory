# Complexes of modules

Native Aglib interfaces and local extensions retain the original complexes,
linear maps, chosen bounds and chain homotopies. Native finite-parametrix and
linear-map cone files, local `SplitPivot`, and the finite-domination files give
actual finite-projective replacements and their signed degree coordinates. `ProjectiveStabilization` constructs the stated
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

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.Aglib.Algebra.Homology.ModuleCat.FiniteProjectiveResolution` | Actual finite-projective resolutions and finite-free PID resolutions |

The current finite-projective resolution interface is
[`FiniteProjectiveResolution`](FiniteProjectiveResolution.lean).

## Native finite-model owners

- [`Aglib.Algebra.Homology.ModuleCat.FiniteParametrix`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Homology/ModuleCat/FiniteParametrix.lean)
- [`Aglib.Algebra.Homology.ModuleCat.LinearMapConeShift`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Homology/ModuleCat/LinearMapConeShift.lean)
- [`Aglib.Algebra.Homology.ModuleCat.LinearMapConeIso`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Homology/ModuleCat/LinearMapConeIso.lean)
- [`Aglib.Algebra.Homology.ModuleCat.LaurentProjectorCech`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Homology/ModuleCat/LaurentProjectorCech.lean)
- [`Aglib.Algebra.Homology.ModuleCat.LaurentModuleCech`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Homology/ModuleCat/LaurentModuleCech.lean)

The finite-parametrix and linear-map cone declarations use `ModuleCat`.
Projector chart existence uses `LaurentPolynomial.Projector`; module chart
existence uses `ModuleCat.LaurentCech`. The retained local `LaurentCech`
extension now uses `LaurentPolynomial.Cutoff`; other local module-complex
extensions retain `Quillen.ModuleComplex`. Scalar coordinate comparisons use
[`Aglib.Algebra.Category.ModuleCat.FiniteMatrixBaseChange`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Category/ModuleCat/FiniteMatrixBaseChange.lean).
The native cone prerequisites are [`Aglib.Algebra.Homology.MappingCone.Parametrix`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Homology/MappingCone/Parametrix.lean)
and [`Aglib.Algebra.Homology.MappingCone.Iso`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Homology/MappingCone/Iso.lean); split product exactness is in
[`Aglib.Algebra.Homology.ShortComplex.ProductSequence`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Homology/ShortComplex/ProductSequence.lean).
