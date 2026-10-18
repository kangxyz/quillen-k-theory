# Local coefficients and homological recognition

## Public imports

Module paths are relative to `Quillen.` unless fully qualified.

| Import | Interface |
| --- | --- |
| [`Quillen.Topology.LocalCoefficients.PullbackCoveringHomology`](PullbackCoveringHomology.lean) | Actual covering-fiber local system and original integral pullback-chain arrow comparison, in one common space universe and without connectedness or pi1-map hypotheses |
| [`Quillen.Topology.LocalCoefficients.PullbackCoveringHomologyUniverseLift`](PullbackCoveringHomologyUniverseLift.lean) | Original chain-arrow comparison with source `Type u` and target/cover `Type (max u v)`; exact successor-universe integral-chain specialization |
| [`Quillen.Topology.LocalCoefficients.H2CapDescent`](H2CapDescent.lean) | For an actual injective map from a path-connected space to a simply connected space with surjective original integral H2, the original connecting image lies in the commutator of the original constant-path fiber pi1 |
| [`Topology.LocalCoefficients.CommonUniverseChains`](CommonUniverseChains.lean) | `Quillen.LocalCoefficients.CommonUniverseChains.liftMap`, `original_chainMap_retract_square`, `all_localCoefficients_liftMap` |
| [`Topology.LocalCoefficients.FirstObstruction`](FirstObstruction.lean) | Absolute first obstruction from lower homotopy and degree-n homology vanishing |
| [`Topology.LocalCoefficients.HomologicalWhiteheadSimplyConnected`](HomologicalWhiteheadSimplyConnected.lean) | Original integral homology isomorphisms imply complete weak equivalence for simply connected same-universe spaces |
| [`Topology.LocalCoefficients.TwistedWhiteheadSuppliedCovers`](TwistedWhiteheadSuppliedCovers.lean) | Original base-map weak equivalence with supplied simply connected covers and commuting lift |

## Absolute first obstruction and homological weak equivalence

`Topology.LocalCoefficients.FirstObstruction` proves the absolute first obstruction for `n = m + 2`: path
connectedness, vanishing of actual positive Pi k for 0<k<n at every point,
and vanishing of genuine degree-n integral homology imply that the original
Pi n at the specified point is a singleton. The ordinary singular-homology
formulation and boundary-fixed nullhomotopy detection retain the original
maps. The coefficients are `ModuleCat.of ℤ (ULift.{u} ℤ)` in the same universe
as the space. Finite chain evaluation uses the actual signed spherical addition
and full relative straightening. This is not a general Hurewicz comparison
isomorphism in every degree. See the [first-obstruction client](../../../examples/downstream/Consumer/FirstObstruction.lean).

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
See the [homological Whitehead client](../../../examples/downstream/Consumer/HomologicalWhiteheadSimplyConnected.lean).

This theorem needs no CW-type or universal-cover-existence assumption. A weak
equivalence is not an asserted continuous homotopy inverse for arbitrary spaces;
upgrades use the precise hypotheses of existing realization/Whitehead or
supplied-domination results. The supplied-cover twisted theorem below gives a bounded nonsimply-connected
recognition result with its actual covers, lift and coefficient hypotheses.

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
convention. The [supplied-cover client](../../../examples/downstream/Consumer/TwistedWhiteheadSuppliedCovers.lean)
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
The [path-class covering client](../../../examples/downstream/Consumer/PathClassCovering.lean)
checks the actual surjective covering. The
[`PathClassEndpoint`](../Covering/PathClassEndpoint.lean)
and [`PathClassSimplyConnected`](../Covering/PathClassSimplyConnected.lean)
prove the actual lifted endpoint equation, path connectedness and uniqueness
of upstairs path classes in that same prebundle topology. In particular,
`PathThinNeighborhoods.total_simplyConnectedSpace` proves genuine simple
connectedness. The [universality client](../../../examples/downstream/Consumer/PathClassUniversality.lean)
checks these literal endpoint and total-space conclusions.
