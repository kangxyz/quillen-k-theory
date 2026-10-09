# Actual fixed-zero grid and exact-functor homotopies

## Contract

These companion modules use the frozen genuine nerve-direction cylinder. They
retain the original simplicial and topological endpoint maps and separate
unbased existence from basedness proved by explicit chosen-zero equalities.

### Actual zero-grid constancy

`NerveCylinderZero.lean` proves
`nerveCylinderDiagram_eq_const_of_zero η Z hZ hA hB τ`.
Its inputs are an actual natural transformation between grid functors, an
actual zero object `Z`, and objectwise equalities of both endpoint functors to
`Z`. Its conclusion is equality of the entire cylinder functor to the constant
`Z` diagram, at every ordinal time. Object equality follows by selecting one
endpoint; map equality follows from zero-object uniqueness. Neither weakness
nor an assumed identity of the transformation at zero is needed for this
lemma.

### Compatible family fixed vertices

`WeakGridBasedHomotopy.lean` exposes `diagonalZeroVertex W`,
`weakGridFamilyCylinder_fixed_vertex`, and
`diagonalWeakGridRealizationHomotopy_fixed_vertex`.
Besides the unbased family's ordinary componentwise reindexing compatibility,
these take a source vertex and objectwise chosen-zero equalities for the two
endpoint grids on every degeneracy of that vertex. They prove that the entire
simplicial vertex track is strictly constant and that its actual realization
stays at the chosen-zero vertex. A fixed-track equation is not assumed.

This is suitable for normalized additivity families once their actual
chosen-zero formulas have separately been proved; these companions do not
prove those normalization formulas or the based additivity theorem.

### Original exact-functor S-maps

`WeakNaturalTransformation.lean` specializes to genuine Waldhausen-exact
functors `F, G` and an actual pointwise weak transformation `η : F ⟶ G`.
`weakNaturalTransformationHomotopy` has exactly the existing `sSetMap hF` and
`sSetMap hG` as endpoints. Its component is definitionally the nerve cylinder
of the actual whiskered transformation, not a map defined by conjugating an
already-known K-equivalence. `weakNaturalTransformationRealizationHomotopy`
has exactly `deloopingMap hF` and `deloopingMap hG` as endpoints.

`WeakNaturalTransformationBased.lean` additionally requires the explicit
object equalities `F.obj V.zero = W.zero` and `G.obj V.zero = W.zero`.
It proves the actual simplicial zero track is constant, the realized homotopy
stays at `W.kBasepoint`, and packages a genuine `ContinuousMap.HomotopyRel`
relative to `{V.kBasepoint}`. The transformation's identity component at zero
follows from zero uniqueness; it is not a separate assumption.

All categories have arbitrary object and hom universes. The actual
S-set/realization map wrappers use a common object universe and a common hom
universe for source and target, matching the existing `sSetMap` API; no
cross-universe identification is claimed. No preadditivity, exact-category,
abelian, or extra homotopy-equivalence hypothesis occurs.

## Verification

The companion audit is `audits/WaldhausenWeakGridBasedAudit.lean`. It scans all
four defining module origins, including private/generated declarations,
recursively permitting only `propext`, `Classical.choice`, and `Quot.sound`.
Consumers retain independent object/hom universes and the exact original
simplicial/realization maps, and test the fixed chosen-zero point.

The initial audit and all consumers passed **22** origins. The expected22
rerun and clean four-source check are recorded in:
- `logs/waldhausen-weak-grid-20261009/based-final-check.log`
- `logs/waldhausen-weak-grid-20261009/based-audit.log`

Frozen source manifest:
`logs/waldhausen-weak-grid-20261009/based-sources.sha256`

Manifest SHA-256:
`5b2f03780bb4444fa9956d8154633941c5b2b338db981f6ed51601e15c1d841a`

This is an authored prerequisite report. Independent acceptance remains with
the separate reviewer; the additivity families' zero normalization is still a
separate proof obligation at this boundary.
