# The actual mixed ordinal cylinder

The seven implementation modules listed in
`logs/mixed-ordinal-cylinder-sources.sha256` are frozen. They construct the
variable-suffix cylinder needed by the explicit Waldhausen additivity deformation,
including its outer-only bisimplicial version. No cylinder homeomorphism or
comparison equivalence is assumed.

## Indexing and exact endpoints

All declarations are in `Quillen.MixedOrdinalCylinder`.

For a monotone cut `φ : [n] → [1]`, `mixedOrdinal φ` is the increasing enumeration
of the ordered subset of `[n] ⋆ [n]` containing every first-copy vertex and
precisely the second-copy vertices with `φ(i)=1`. Thus it is the full first copy
followed by a repeated terminal segment. `mixedMap` is induced by the actual
ordinary join map, permitting a pointwise inclusion of selected terminal segments.
This construction is natural under arbitrary ordinal maps; preservation of the
last vertex is not assumed.

- `firstIndex φ` and `switchedIndex φ` are monotone maps from `[n]`. The latter
  uses the first copy when `φ(i)=0` and the repeated copy when `φ(i)=1`.
- `firstIndex_le_switchedIndex` and `switchedIndex_naturality` provide the exact
  inequalities and reindexing needed by the arrow-valued additivity diagram.
- `zeroIso n` identifies the zero-cut mixed ordinal with `[n]`, using the actual
  first-copy maps. `oneIso n` identifies the one-cut mixed ordinal with the
  ordinary join, using the actual ambient inclusion.
- `firstIndex_one_le_switchedIndex n i j` says every first-copy vertex precedes
  every switched vertex at the one cut, including unequal indices.

## Actual simplicial and bisimplicial models

`cylinder X` has simplices `Σ φ, X[mixedOrdinal φ]`; its face and degeneracy maps
pull back the cut and restrict the mixed ordinal. `zeroSection`, `oneSection`,
and `projection` are actual natural transformations, with proved exact identities:

- `zeroSection X ≫ projection X = 𝟙 X`;
- `oneSection X ≫ projection X = OrdinalSubdivision.endpoint X`.

`minCut φ τ` intersects the selected terminal segment with the simplicial interval
parameter. Restriction along its inclusion gives `contraction`, a genuine
simplicial homotopy from `projection X ≫ zeroSection X` to the identity.
Constant-cut identifications use proved equality transport of the actual ordinal
maps; no dependent equalities are treated as definitional without proof.

For `X : SimplexCategoryᵒᵖ ⥤ SSet`, `outerCylinder X` keeps the inner degree fixed:

`((outerCylinder X).obj n).obj m = Σ φ : Cut n.unop, (X.obj (op (mixedOrdinal φ))).obj m`.

This object is separately functorial in both degrees. `outerProjection`,
`outerZeroSection`, and `outerOneSection` are bisimplicial maps, and their composite
identities are proved strictly. `outerContraction` is a direct simplicial homotopy
on the actual diagonal, changing only the outer mixed ordinal. It does not
replace the inner nerve degree by a subdivided degree.

## Realization interfaces

- `projectionRealizationHomotopyEquiv X` and
  `oneSectionRealizationHomotopyEquiv X` compare the ordinary mixed-cylinder
  realization with its zero and one endpoints.
- `outerProjectionRealizationHomotopyEquiv X` and
  `outerOneSectionRealizationHomotopyEquiv X` give the corresponding actual
  bisimplicial-diagonal comparisons.

Every forward map is definitionally the realization of the named canonical
simplicial map. Projection equivalences use the explicit min-cut homotopy and
actual zero section. One-section equivalences cancel projection against the
previously checked ordinary first-half subdivision equivalence.

This is topology support for additivity. It does not by itself assert the
cofibration algebra, the additivity comparison map, or normalized based K-map
naturality of that future comparison.

## Verification

All seven modules have passed focused source checks without warnings. The final
ordered source recheck, recursive audit of all 183 declaration origins, and exact-map
consumer audit are recorded in `logs/mixed-final-*.log` and
`logs/mixed-ordinal-cylinder-audit.log`. The audit includes arbitrary realization
universe, actual unchanged inner degree, endpoint ordinal maps, direct simplicial
homotopies, and exact forward maps. The only permitted recursive axiom dependencies
are `propext`, `Classical.choice`, and `Quot.sound`. The fixed-183-count rerun
passed, and every frozen implementation source hash matched afterward.
