# Homological and metric homotopy foundations

The library proves signed spherical addition, full finite relative
straightening, first-obstruction consequences and simply connected homological
weak Whitehead. Its geometric foundations include actual weak/metric
realization equivalence, local metric equiconnection, compact-open loop geometry
and constructed numerable realization domination. These supply the exact
standard original-Q comparison homotopy equivalence and the original K₀–plus
product described in the [ring plus guide](PlusConstruction.md).

Use `Quillen.Topology` for the combined surface or the focused owners below.
The [classical CW plus guide](ClassicalCWPlus.md) records the automatic
same-universe and mixed-universe comparisons on original actual Hausdorff CW
spaces, ordinary uniqueness, constructed covers and explicit coefficient
bounds. The [scope reference](../reference/Scope.md#verification) records the
current integrated checking scope.

## Supplied coverings and regular chains

`Topology.Realization.SimplexConnectivity`, `Topology.Covering.SingularSimplices`
and `Topology.Covering.PathClasses` construct the connectivity and actual
lifting/path-class tools for a supplied covering. `Topology.LocalCoefficients`
owners `RegularChains`, `CoveringChains`, `RegularFunctoriality` and
`CoveringNaturality` supply the displayed regular-chain identification and its
functoriality. The regular-chain identification requires a supplied cover with
simply connected total space and a chosen point; arbitrary-cover lifting is a
separate result. Its common-model universe and explicit `ULift` coefficient
convention are part of the statements.

These chain identifications retain the displayed supplied cover and its
simply connected total space. The path-class endpoint/universality construction
below now proves simple connectedness for its actual chart-topologized total
space under the stated local geometric assumptions. This does not remove
hypotheses from unrelated supplied-cover interfaces. The
[covering-chain client](../../examples/downstream/Consumer/RegularCoveringChains.lean)
and the [path-class client](../../examples/downstream/Consumer/CoveringPathClasses.lean)
exercise the actual maps and paths.

## Relative obstruction and cone homology

`Topology.HomotopyCofiber.UnreducedFirstObstruction` uses the actual iterated
fiber-path and simply-connected interfaces to prove relative first-obstruction
geometry. The constant-chain, mapping-cylinder, point-relative and finite-boundary
owners culminate in `Topology.HomotopyCofiber.UnreducedConeHomology`: actual
relative finite-chain witnesses and positive homology vanishing for the
unreduced cone, starting from the original constant-chain `QuasiIso` hypothesis. The full relative-homology/cone comparison isomorphism is not
implemented; its critical-path vanishing consequence is available.

See [first-obstruction](../../examples/downstream/Consumer/UnreducedFirstObstruction.lean),
[finite relative-boundary](../../examples/downstream/Consumer/PointRelativeHomology.lean)
and [cone-homology](../../examples/downstream/Consumer/UnreducedConeHomology.lean)
clients for the displayed hypotheses and maps.

## Spherical representation and quotient descent

`Topology.HomotopyGroups.SphericalSimplex` and `SphericalSimplexParametrization`
prove spherical representation and parameterized vanishing detection.
`Topology.Cube.StickBreaking`, `StickBreakingFaces` and
`Topology.HomotopyGroups.SphericalSimplexQuotient` prove the actual noninjective
stick-breaking quotient, genuine cube/homotopy descent and ordered lower/upper
face formulas in the original homotopy groups.

A quotient is not being promoted to a homeomorphism. The new `Cube.FaceFold`,
`CoordinateFaceFold`, `HomotopyGroups.CubicalFaceFold`, `CubicalUpperFaceFold`,
`CubicalBoundaryInduction` and `SphericalHomotopyAddition` owners prove the
actual geometric signed-addition relation in degree n=m+2. The generic ordered
lower and upper face operations retain their noncommutative order; commutativity
is used only in the positive higher group where it is available. The proof
uses explicit folding homotopies and genuine finite induction, not an assumed
addition certificate. See the [signed-addition client](../../examples/downstream/Consumer/SphericalHomotopyAddition.lean).
The [stick-breaking client](../../examples/downstream/Consumer/StickBreaking.lean)
uses the proved quotient and face interface.

## Full finite relative straightening

The bounded `FiniteSimplexFamily`, `SimplexBoundaryFilling`, `SimplexFaceGluing`
and `SimplexStraighteningStep` owners feed `Topology.Realization.SimplexSkeleton`,
`FiniteSimplexStraightening` and `RelativeSphericalStraightening`. Together they
prove full finite relative dimension induction, using path connectedness
and actual `Pi k` vanishing only for `0 < k < n`.

The fixed family consists of the specified spherical input/faces and
basepoint-constant simplices. Arbitrary constant simplices at other target
points are not silently included. The straightening statement supplies no
coefficient transport or chain homotopy; the first-obstruction and homological
Whitehead assembly below is a separate theorem chain.
The [full finite-straightening client](../../examples/downstream/Consumer/FiniteSimplexStraightening.lean)
retains the displayed family, vanishing range and actual straightening maps.

## Absolute first obstruction and homological weak equivalence

`Topology.LocalCoefficients.FirstObstruction` proves the absolute first obstruction for `n = m + 2`: path
connectedness, vanishing of actual positive Pi k for 0<k<n at every point,
and vanishing of genuine degree-n integral homology imply that the original
Pi n at the specified point is a singleton. The ordinary singular-homology
formulation and boundary-fixed nullhomotopy detection retain the original
maps. The coefficients are `ModuleCat.of ℤ (ULift.{u} ℤ)` in the same universe
as the space. Finite chain evaluation uses the actual signed spherical addition
and full relative straightening. This is not a general Hurewicz comparison
isomorphism in every degree. See the [first-obstruction client](../../examples/downstream/Consumer/FirstObstruction.lean).

`Topology.HomotopyGroups.Connectivity.FiberObstructionStep`,
`Topology.HomotopyCofiber.HomologicalFirstObstruction` and
`Topology.LocalCoefficients.HomologicalWhiteheadSimplyConnected` assemble simply connected homological weak Whitehead.
For simply connected X,Y in the same universe and the original continuous map
f, isomorphisms of all its ordinary integral singular-homology maps imply
complete `IsWeakHomotopyEquivalence f`. The constant-chain `QuasiIso` formulation
is proved first and connected to the original homology maps by their actual
natural comparison. At m=0 the fiber Pi 1 may be nonabelian; the proof does not
replace it by an abelian group. Arbitrary fiber points use their stored paths,
basepoint transport and a genuine connecting path in the proved connected fiber.
See the [homological Whitehead client](../../examples/downstream/Consumer/HomologicalWhiteheadSimplyConnected.lean).

This theorem needs no CW-type or universal-cover-existence assumption. A weak
equivalence is not an asserted continuous homotopy inverse for arbitrary spaces;
upgrades use the precise hypotheses of existing realization/Whitehead or
supplied-domination results. The supplied-cover twisted theorem below gives a bounded nonsimply-connected
recognition result with its actual covers, lift and coefficient hypotheses.

## Metric realization equivalence and local equiconnection

`Topology.MetricOrderComplex.RealizationReconstruction` proves exact set-level
reconstruction. `FiniteCharts`, `CutoffRealization`,
`Topology.Realization.CylinderContinuity` and `RealizationHomotopyEquiv` supply
a continuous cutoff-reconstruction reverse map to the original coordinate map,
with actual homotopies fixed at every vertex and a compact-open based-loop
homotopy equivalence. The unrestricted raw set inverse is not asserted
continuous, and no homeomorphism between the two topologies is claimed.
See the [metric-equivalence client](../../examples/downstream/Consumer/MetricOrderHomotopyEquiv.lean).

`CommonMass`, `CommonPoint`, `CommonPointContinuity`, `AffineSegment` and
`Equiconnection` prove a jointly continuous local connector on the open domain
of positive common mass, equivalently L1 distance less than two. The identity
`2 * commonMass + distance = 2` controls moving-support tails. Two affine
segments pass through the normalized common point; each support is a genuine
chain, using intersection support rather than a false union-chain claim.
The connector has exact endpoints and fixes the whole diagonal. Shared positive
coordinates persist, yielding connector-convex open vertex stars. See the
[metric-connector client](../../examples/downstream/Consumer/MetricOrderEquiconnection.lean).

## Compact-open loop geometry

`Topology.LocalEquiconnection.Loops` constructs the pointwise connector on
literal based paths with their original compact-open topology. Compactness
of the interval proves that its permitted pair domain is open; the
whole-diagonal identity fixes both endpoints. `LoopConvexCover` shrinks a
finite interval subcover to compact pieces, producing actual open
connector-convex neighborhoods of every based loop. `Topology.PathSpace.Metric`
retains the original path topology.

`Topology.MetricOrderComplex.LoopEquiconnection` applies these constructions
to metric-order vertex loops, with an actual convex-open cover. The
[loop-geometry client](../../examples/downstream/Consumer/MetricOrderLoops.lean)
checks the maps and neighborhoods. The existing
`Topology.HomotopyEquiv.BasedReplacement`, `BasedLoop` and
`Topology.ClassifyingSpace.PosetLoop` interfaces supply the compact-open loop
comparison used to transport this geometry.

## Actual numerable nerve domination

`Topology.MetricSpace.CoverRadius` constructs a positive Lipschitz subordinate
radius for an arbitrary open cover of a metric space. Its one-eighth balls
give the actual point-star refinement in `MetricPointStarRefinement`.
Metric paracompactness supplies a subordinate partition of unity. No uniform
Lebesgue number or compactness of the metric space is assumed.

`OrderedConnectorInterpolation`, `ConnectorSimplexFaces` and
`ConnectorMonoCoherence` construct order-sensitive finite interpolation,
carrier preservation, and face/mono coherence. The raw interpolation is not
asserted coherent under degeneracies. `OrderedNerveRealizationMap` instead
defines `nerveReturnMap` through the nondegenerate-simplex colimit. On a
degenerate simplex, its canonical epimorphism to the unique nondegenerate
image first pushes forward and sums repeated weights, before interpolation.
No associativity of the local connector is assumed.

`FiniteNerveCharts` and `POUNerveClassifier` construct `partitionNerveMap`
into the actual weak ordered-cover-nerve realization, using the original
partition coefficients. Local finite closed-support control proves continuity
in that weak topology; coordinatewise continuity is not a replacement.
`NumerableRealizationDomination` uses point-star convex carriers and the
original connector to construct `numerableDominationHomotopy`, from the
actual return-after-classifier composite to the identity. Its theorem
`exists_numerable_realization_domination` constructs the simplicial set,
both continuous maps and the homotopy from the displayed cover, vertices,
convexity, point-star refinement and subordinate partition data.

`MetricRealizationDomination` derives these inputs for a metric space with an
actual local connector and open connector-convex cover. Thus
`MetricOrderComplex.LoopDomination` constructs domination for the literal
metric-order loop space, and `ClassifyingSpace.LoopDomination` transports it
to original categorical loops. `RankedChainOrder.universalLoopDominationData`
retains independent object and morphism universes `u, v`, with a simplicial
model in `max u v`. A chosen inverse or domination certificate is not an
input to this construction. This is the geometric bridge used by the exact original-Q comparison.
See the [nerve-return](../../examples/downstream/Consumer/OrderedNerveReturn.lean)
and [numerable-domination](../../examples/downstream/Consumer/NumerableDomination.lean)
clients.

## Supplied-cover twisted Whitehead and path-class coverings

`Topology.LocalCoefficients.RegularIsomorphism`, `CoveringHomologyComparison`
and `TwistedWhiteheadSuppliedCovers` transport the original twisted chain
maps to ordinary integral homology of an actual commuting lift. Simply
connected homological weak Whitehead applies to the supplied total spaces, and
`Topology.Covering.HomotopyGroups` descends the higher homotopy isomorphisms.
With path-connected bases and the displayed fundamental-group isomorphism,
`isWeakHomotopyEquivalence_of_twisted_quasiIso_suppliedCovers` proves complete
weak equivalence of the original base map. All four space universes and the
coefficient universe are the same `u`; the hypothesis quantifies all
`System.{u, u}` target systems using the explicit `UniverseLift.chainMap`.
It does not erase the ring-plus certificate's separate `u + 1` coefficient
convention. The [supplied-cover client](../../examples/downstream/Consumer/TwistedWhiteheadSuppliedCovers.lean)
retains the cover projections, lift and commuting equation.

`Topology.Covering.PathClassPrebundle` constructs a surjective covering on
the literal dependent based-path-class total space. Its geometric input is
`PathThinNeighborhoods`, together with path connectedness and local path
connectedness of the original base. The open path-connected neighborhoods
are ambient-thin: two paths in one neighborhood with the same endpoints
are homotopic in the base, without asserting the homotopy stays in the
neighborhood. Transition functions are locally constant; arbitrary local
path choices are not assumed continuous.

`LocalConnectorHypotheses` supplies these local inputs from an actual
continuous local connector on the original space. The independent
`Realization.ColimitLocallyPathConnected` argument proves local path
connectedness for an actual topological colimit of locally path-connected
objects; it does not prove semilocal simple connectedness.
The [path-class covering client](../../examples/downstream/Consumer/PathClassCovering.lean)
checks the actual surjective covering. The newly included
[`PathClassEndpoint`](../../Quillen/Topology/Covering/PathClassEndpoint.lean)
and [`PathClassSimplyConnected`](../../Quillen/Topology/Covering/PathClassSimplyConnected.lean)
prove the actual lifted endpoint equation, path connectedness and uniqueness
of upstairs path classes in that same prebundle topology. In particular,
`PathThinNeighborhoods.total_simplyConnectedSpace` proves genuine simple
connectedness. The [universality client](../../examples/downstream/Consumer/PathClassUniversality.lean)
checks these literal endpoint and total-space conclusions.

## Actual CW geometry and automatic plus uniqueness

The included classical-CW owners construct characteristic quotients, skeletal
and global lifting, homotopy lifting and Whitehead recognition directly from
actual Hausdorff CW subtypes. No finite-dimensional, countable or locally
finite condition is added. The actual weak map is retained as the forward map
of `ClassicalCW.homotopyEquivOfWeakHomotopyEquivalence`.

`ClassicalCW.locallyPathConnectedSpace` and `pathThinNeighborhoods` construct
the local geometric inputs from the original CW cells and topology.
`ClassicalCW.exists_simplyConnected_cover` then constructs a same-universe
surjective covering with simply connected total space for an actual connected
Hausdorff CW subtype. It does not assume a supplied universal cover.

The actual canonical double cylinder has constructed connectivity, local path
connectedness and thin neighborhoods. Its path-class cover and those of both
ends supply `IsPlusConstruction.classicalCWPlusUnique`, whose only geometric
inputs are the original actual Hausdorff CW subtypes and original same-universe
plus certificates. Ordinary uniqueness follows by self-cylinder homotopy
cancellation. See [ClassicalCWPlus.md](ClassicalCWPlus.md) for the exact maps,
points, tracks, subgroup, and distinction from prescribed-track coherence.

The lower-level chosen-cover branch remains available with explicit actual
covers, cover points, target-cover surjectivity and pushout data; it constructs
the commuting lifts. The separate cover-transfer owners prove actual pullback
covering and simple-connectedness results under a supplied homotopy equivalence
to a local-connector space. Their categorical-realization specialization uses
the constructed resolution and weak/metric equivalences; it does not identify
an arbitrary CW-homotopy-type model with a nerve.

## Generic component products

`Topology.HomotopyEquiv.ComponentSigma`,
`Topology.HomotopyGroups.Loop.ComponentProduct` and
`NormalizedComponentProduct`, with `Topology.Realization.OpenComponents`,
construct generic component products and their normalized identity slice at
the exact assumptions. See the
[component-product client](../../examples/downstream/Consumer/LoopComponentProduct.lean).

The displayed right concatenation is order-sensitive. The standard product
retains the order of its actual zero-component loop and selected representative.
`KTheory.GrothendieckComparison.ContinuousLoopLabels` and `LoopComponentProduct`
now specialize this geometry to original Q loops with the continuous discrete
original K₀ classifier, normalized neutral slice, representative-change
homotopies and ordinary forward-map naturality. The final
`KTheory.Plus.ProjectiveOriginalPlusProduct` replaces the neutral-loop factor
by the specific original plus-certified completion component through the
exact standard equivalence. Its positive labels and track are retained.
No natural chosen inverse, H-space, A∞ or infinite-loop splitting is asserted.

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
asserted natural. See [mathematical scope](../reference/Scope.md).
