# Topology

The library proves signed spherical addition, finite relative straightening,
first-obstruction consequences and simply connected homological weak Whitehead.
Its geometric constructions retain actual spaces, maps, paths and topologies.
Use `Quillen.Topology` for the combined surface or a focused module below.

## Source-family guides

| Family | Objects and interfaces |
| --- | --- |
| [Homotopy groups](HomotopyGroups/README.md) | Spherical representation, signed addition and loop reversal |
| [Realization](Realization/README.md) | Finite relative straightening and exact-forward Whitehead |
| [Local coefficients](LocalCoefficients/README.md) | First obstruction, ordinary and twisted homological recognition |
| [Coverings](Covering/README.md) | Supplied covers, path classes and pullback interfaces |
| [CW complexes](CWComplex/README.md) | Actual CW lifting, Whitehead and constructed covers |
| [Classical CW plus](PlusConstruction/ClassicalCW.md) | Automatic comparison, ordinary uniqueness and universe transport |
| [Metric order complexes](MetricOrderComplex/README.md) | Weak/metric realization equivalence and constructed domination |
| [Local equiconnection](LocalEquiconnection/README.md) | Original-space and compact-open connector modules |
| [Path spaces](PathSpace/README.md) | Compact-open loop geometry |
| [Homotopy equivalences](HomotopyEquiv/README.md) | Component products and their order conventions |
| [Homotopy cofibers](HomotopyCofiber/README.md) | Relative obstruction and cone-homology vanishing |
| [HELP](HELP/README.md) | Finite cube lifting and cone-fiber excision bounds |
| [Prespectra](Prespectrum/README.md) | Signed stable fibers, categorical localization and telescopes |

The geometric foundations supply the exact original-Q comparison and K₀–plus
product; their application contracts belong to the
[ring plus family](../KTheory/Plus/README.md). Verification coverage and collective
limits remain in the [scope summary](../../docs/reference/Scope.md).

## Public imports

Module paths are relative to `Quillen.` unless fully qualified.

| Import | Interface |
| --- | --- |
| [`Quillen.Topology.HomotopyFiber.LoopCentrality`](HomotopyFiber/LoopCentrality.lean) | Actual right loop concatenation and centrality of the original connecting image and fiber-projection kernel, without connectivity assumptions |
| [`Quillen.Topology.HomotopyFiber.SourceContractionBoundary`](HomotopyFiber/SourceContractionBoundary.lean) | Original connecting map computed from actual source-coordinate contraction, based cancellation and the inverse loop-shift formula |
| [`Quillen.Topology.HomotopyFiber.WeakBasePositive`](HomotopyFiber/WeakBasePositive.lean), `HomotopyPiOneNaturality` | Original fiber-pi1 comparison for weak base changes and arbitrary homotopy squares, with mixed space universes and nonstationary vertex tracks |
| [`Quillen.Topology.HomotopyFiber.InjectiveH2Perfectness`](HomotopyFiber/InjectiveH2Perfectness.lean), `H2Perfectness` | Actual homotopy-fiber pi1 is perfect for path-connected perfect-pi1 source, simply connected target and surjective original integral H2; genuine mapping-cylinder reduction and original quasi-isomorphism corollaries |
| [`Quillen.Topology.ClassifyingSpace.NaturalTransformationLoopCancellation`](ClassifyingSpace/NaturalTransformationLoopCancellation.lean) | Whole jointly continuous cancellation prism for composed natural-transformation tracks, preserving the actual endpoints |
| [`Quillen.Topology.PlusConstruction.ClassicalCWUniqueness`](PlusConstruction/ClassicalCWUniqueness.lean) | Automatic comparison and ordinary uniqueness for original plus maps on actual same-universe Hausdorff CW spaces; `Quillen.IsPlusConstruction.exists_classicalCWComparison`, `classicalCWHomotopyCancel`, `homotopic_classicalCWComparisons`, `classicalCWPlusUnique` |
| [`Quillen.Topology.PlusConstruction.ClassicalCWUniquenessUniverseLift`](PlusConstruction/ClassicalCWUniquenessUniverseLift.lean) | Mixed-universe comparison and ordinary uniqueness on the original actual CW spaces; `Quillen.IsPlusConstruction.exists_classicalCWComparison_commonUniverse`, `classicalCWHomotopyCancelCommonUniverse`, `homotopic_classicalCWComparisons_commonUniverse`, `classicalCWPlusUnique_commonUniverse`, `classicalCWPlusUnique_successor` |
| [`Quillen.Topology.DeformationRetract.Basic`](DeformationRetract/Basic.lean) | Cylinder deformation retracts and pushout transport |
| [`Quillen.Topology.MappingCylinder.Basic`](MappingCylinder/Basic.lean) | Interval maps, cylinder projections, and retracts |
| [`Quillen.Topology.UnitInterval`](UnitInterval.lean) | Shared interval multiplication continuity |
| [`Quillen.Topology.Pushout.HomotopyEquivalence`](Pushout/HomotopyEquivalence.lean) | Homotopy gluing and specified component maps |
| [`Topology.PlusConstruction.UnivSubtype`](PlusConstruction/UnivSubtype.lean) | `Quillen.PlusConstruction.UnivSubtype.isPlusConstruction`, `liftPath_apply`, `kernel_lift`, `forward_down` |
| [`Topology.PlusConstruction.ClassicalCWComparison`](PlusConstruction/ClassicalCWComparison.lean), [`Topology.PlusConstruction.ClassicalCWComparisonUniqueness`](PlusConstruction/ClassicalCWComparisonUniqueness.lean) | Chosen-cover existence and ordinary uniqueness, retaining the covers, points, surjectivity and pushout inputs |
| [`Topology.PlusConstruction.CommonUniverse`](PlusConstruction/CommonUniverse.lean) | `Quillen.PlusConstruction.CommonUniverse.isPlusConstruction`, `basedPiOneMap_square`, `kernel_lift`, `liftPath_down`, `forward_down` |
| [`Topology.ClassifyingSpace.LoopDomination`](ClassifyingSpace/LoopDomination.lean) | `RankedChainOrder.universalLoopDominationData` for original loops with independent categorical universes |
| [`Topology.ClassifyingSpace.SimplyConnectedCover`](ClassifyingSpace/SimplyConnectedCover.lean) | Constructed simply connected cover of an original path-connected categorical realization |

## Universe and comparison boundaries

Common-universe chain/certificate transport and actual CW subtype/ULift geometry
support the original-space mixed-universe assembly.
`classicalCWPlusUnique_successor` consumes the original
`IsPlusConstruction.{u,u+1,u+1}` certificates. General mixed ambient universes
`u`, `v`, `w` require all target systems in `U = max u v w z` in the original
certificates. These adapters do not enlarge a smaller coefficient quantifier.

Arbitrary CW-homotopy-type transport and prescribed-track coherent uniqueness
are not supplied. The original-Q homotopy equivalence and product retain the
exact standard maps and original plus model; their chosen inverses are not
asserted natural. See [mathematical scope](../../docs/reference/Scope.md).
