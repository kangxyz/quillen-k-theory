# Actual two-sided bar bridge to diagonal realization

## Checked endpoint

The seven `Quillen/Topology/Realization/TwoSidedBar*.lean` modules construct a
natural zigzag of genuine realization homotopy equivalences

```
|replacementDiagonal (liftedDiagram H)|  ←  |diagonalSSet (bar H)|  →  |diagonalSSet H|.
```

The two actual forward maps are the original coordinate-dropping augmentation
and the original evaluation augmentation. Their APIs are
`Quillen.TwoSidedBar.dropRealizationHomotopyEquiv` and
`Quillen.TwoSidedBar.evaluationRealizationHomotopyEquiv`, with exact `_toFun`
lemmas. `drop_naturality` and `evaluationMap_naturality` retain strict naturality
in the supplied bisimplicial diagram. `vertex`, `evaluationMap_vertex`, and
`drop_vertex` identify the prescribed original degree-zero vertex on both sides.
No based inverse is asserted or needed.

## Construction and proof

For a small category D, an ordinal diagram L, and a simplicial-set diagram H,
a bar simplex is an indexing chain, an H-simplex at its first vertex, and a
standard-simplex coordinate at its last vertex. Every outer operator keeps both
endpoint transports. In the diagonal application the indexing category is
explicitly `AsSmall SimplexCategoryᵒᵖ`, in the coefficient universe.

Dropping the last coordinate is a rowwise homotopy equivalence: the actual
standard simplex is finite and contractible. Its product comparison is an
accepted finite-factor homeomorphism. Genuine coproduct and rowwise diagonal
invariance then prove the prescribed drop map a realization equivalence.
No unrestricted ordinary-product homeomorphism is used.

For evaluation, fix the inner ordinal q. The transposed bar row is literally
the nerve of the category of triples (d, x, d→q), with transport-compatible
maps. Evaluation sends such a triple to its actual transported simplex in
H(q)(q). Its section is the actual triple (q, y, identity). The supplied
augmentation arrow is a natural transformation from identity to the section
composite, and evaluation followed by the section is naturally isomorphic
to identity on the discrete target. This yields an actual classifying-space
homotopy equivalence. The strict column identification preserves the original
evaluation map. Transposed rowwise diagonal invariance gives the second endpoint.
The argument covers empty coefficient sets without selecting a nonexistent point.

## Validation boundary

All seven sources were rebuilt serially, warning-free, with importable outputs.
Their immutable manifest is `logs/two-sided-bar-sources.sha256`.
The own recursive origin scan passed all 170 declarations and ten exact-map,
naturality, vertex and arbitrary-universe consumers, warning-free. Only standard
axioms occur recursively. The count-frozen audit is `audits/TwoSidedBarAudit.lean`;
its final warning-free pass is recorded in `logs/two-sided-bar-fixed170.log`.
All ten consumers passed, and every source hash matches afterward.

This bridge does not assert the connected-row diagonal fiber theorem. The
finite weak-cartesian gluing theorem and the final identification with the
original canonical Waldhausen fiber map remain separate proof obligations.
