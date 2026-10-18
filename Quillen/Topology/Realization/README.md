# Realization geometry and Whitehead recognition

## Public imports

Module paths are relative to `Quillen.` unless fully qualified.

| Import | Interface |
| --- | --- |
| [`Quillen.Topology.Realization.PrescribedFiniteVertexStraightening`](PrescribedFiniteVertexStraightening.lean), `EmbeddingFiniteVertexStraightening`, `JointFiniteVertexStraightening` | Actual finite face-compatible simplex tracks fixing prescribed based subfamilies, with source-image compatibility constructed using injectivity and boundary HEP |
| [`Quillen.Topology.Realization.Constant`](Constant.lean) | The literal realization of a constant simplicial map |
| [`Quillen.Topology.Realization.Skeleton`](Skeleton.lean) | The bottom simplicial skeleton |
| [`Quillen.Topology.Realization.SubfamilyHEP`](SubfamilyHEP.lean) | Homotopy extension for realized simplicial subfamilies |
| [`Topology.Realization.RelativeSphericalStraightening`](RelativeSphericalStraightening.lean) | Full finite relative straightening with its specified fixed family |
| [`Topology.Realization.OrderedNerveRealizationMap`](OrderedNerveRealizationMap.lean) | Actual nerve return map using nondegenerate interpolation and canonical-epi weight aggregation |
| [`Topology.Realization.POUNerveClassifier`](POUNerveClassifier.lean) | Original partition-of-unity classifier into the weak realization |
| [`Topology.Realization.NumerableRealizationDomination`](NumerableRealizationDomination.lean), [`Topology.Realization.MetricRealizationDomination`](MetricRealizationDomination.lean) | Constructed realization domination from the displayed cover/connector data |
| [`Topology.Realization.Whitehead`](Whitehead.lean) | Exact-forward homotopy equivalence for weak equivalences between actual simplicial realizations |

## Full finite relative straightening

The bounded `FiniteSimplexFamily`, `SimplexBoundaryFilling`, `SimplexFaceGluing`
and `SimplexStraighteningStep` owners feed `Topology.Realization.SimplexSkeleton`,
`FiniteSimplexStraightening` and `RelativeSphericalStraightening`. Together they
prove full finite relative dimension induction, using path connectedness
and actual `Pi k` vanishing only for `0 < k < n`.

The fixed family consists of the specified spherical input/faces and
basepoint-constant simplices. Arbitrary constant simplices at other target
points are not silently included. The straightening statement supplies no
coefficient transport or chain homotopy; the [first-obstruction and homological
Whitehead assembly](../LocalCoefficients/README.md) is a separate theorem chain.
The [full finite-straightening client](../../../examples/downstream/Consumer/FiniteSimplexStraightening.lean)
retains the displayed family, vanishing range and actual straightening maps.

## Whitehead for actual simplicial realizations

`Quillen.Topology.Realization.Whitehead` constructs
`Realization.homotopyEquivOfWeakHomotopyEquivalence` for the actual realizations
of `X Y : SSet.{u}`. Its forward continuous map is exactly the given weak
homotopy equivalence. A cube/simplex boundary-pair homeomorphism, realized
boundary lifting and skeletal monomorphism lifting construct a global inverse;
the actual simplicial cylinder supplies the second inverse homotopy. No chosen
inverse or target-bearing compact-HELP certificate is assumed.

The inverse homotopies are ordinary, unbased homotopies. The generic
supplied-domination upgrade retains its explicit domination data. For the
original Q-loop comparison, the metric/numerable construction now supplies
that data, so the exact map is genuinely upgraded as recorded in the [ring plus guide](../../KTheory/Plus/README.md). This
does not by itself identify an arbitrary CW-type model or arbitrary plus model.
[`Consumer.RealizationWhitehead`](../../../examples/downstream/Consumer/RealizationWhitehead.lean)
checks the unchanged forward map and actual inverse-homotopy consequences.
