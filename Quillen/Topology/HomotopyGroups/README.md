# Spherical and cubical homotopy groups

## Public imports

Module paths are relative to `Quillen.` unless fully qualified.

| Import | Interface |
| --- | --- |
| [`Quillen.Topology.HomotopyGroups.SelfTrackLoopShift`](SelfTrackLoopShift.lean), [`Quillen.Topology.HomotopyFiber.SelfHomotopy`](../HomotopyFiber/SelfHomotopy.lean) | Signed loop-shift formula and original path-space connecting/self-track compatibility |
| [`Quillen.Topology.HomotopyGroups.Loop.Reversal`](Loop/Reversal.lean) | Actual inner-loop reflection and degree-shift formulas |
| [`Topology.HomotopyGroups.SphericalHomotopyAddition`](SphericalHomotopyAddition.lean) | Genuine signed spherical addition in degree m+2 |

## Spherical representation and quotient descent

`Topology.HomotopyGroups.SphericalSimplex` and `SphericalSimplexParametrization`
prove spherical representation and parameterized vanishing detection.
`Topology.Cube.StickBreaking`, `StickBreakingFaces` and
`Topology.HomotopyGroups.SphericalSimplexQuotient` prove the actual noninjective
stick-breaking quotient, genuine cube/homotopy descent and ordered lower/upper
face formulas in the original homotopy groups.

A quotient is not being promoted to a homeomorphism. The `Cube.FaceFold`,
`CoordinateFaceFold`, `HomotopyGroups.CubicalFaceFold`, `CubicalUpperFaceFold`,
`CubicalBoundaryInduction` and `SphericalHomotopyAddition` owners prove the
actual geometric signed-addition relation in degree n=m+2. The generic ordered
lower and upper face operations retain their noncommutative order; commutativity
is used only in the positive higher group where it is available. The proof
uses explicit folding homotopies and genuine finite induction, not an assumed
addition certificate. See the [signed-addition client](../../../examples/downstream/Consumer/SphericalHomotopyAddition.lean).
The [stick-breaking client](../../../examples/downstream/Consumer/StickBreaking.lean)
uses the proved quotient and face interface.
