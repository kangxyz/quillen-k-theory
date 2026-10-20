# The original global projection carrier

`GlobalRawBassProjectionReference`, `GlobalRawBassProjectionFamily`,
`GlobalRawBassProjectionFourEdgeMap`, `GlobalRawBassProjectionFourEdgeNative` and
`GlobalRawBassProjectionCone` construct an actual scalar carrier for the original
`GlobalRawBass.comparison X`, for an arbitrary scheme `X` and actual Model map
`E : V → Model(X)`.

The namespace is `GlobalRawBass.ProjectionReference`, with the tree and cone
constructions in its `FourEdge` namespace. There are no coefficient `P/Under`
hypotheses and no assumed native-family lift.

## Complete original attachments

`source X` is literally `InputIdentityProjection.source X`. The five `nodes`
are the lexicographic product of an arbitrary complete `Node E` and the original
five projection nodes. `chartNode` accepts every node of the genuine polynomial
reference `E ≫ projectionMap X`; `plus_attachment` and `minus_attachment` identify
the complete nodes, including their original reference isomorphisms.

`beta` is produced by the four displayed double-cylinder pushouts.
`beta_plus`, `beta_minus` and `beta_edge12/01/03/34` retain the complete polynomial
summands and all four original cylinders. `beta_overlap` is an equality in the
Laurent reference realization before native evaluation, using exactly the
original reversed positive halves and unreversed inverse halves.

## Native evaluation and height

`beta_native` identifies the whole tree's comparison value at every native level.
The single unreduced pushout `scalarCone X E` therefore has an actual `coneEval`.
It retains the whole Laurent nerve, both polynomial sectors, all overlap points,
the original cone height and the native cone tip. `scalarCone_contractible`
applies to this same scalar carrier. It does not identify its different baseline
points or assert that native evaluation is injective.

`coneEval_compact_continuous` and `compactConeFamily` give joint continuity on
any supplied compact scalar family and the genuine native input. `coneEval_point`
and `coneEval_structure` preserve the native base point and independent structure
coordinate. `coneEval_overlapCylinder` keeps the overlap time and cone height
separate. No unrestricted globally continuous evaluator is asserted.

## Actual composition polynomial-node attachment

`GlobalRawBassInputCompositionSpanScalarNodes` sets
`E := InputCompositionTopPieces.baseSource f g`. Its `polynomialNode` maps the
original polynomial rectangle reference into `E ≫ projectionMap X` using the
inverse of the original binary normalization iso. `moving_anchor` derives the
complete chart anchor from the already proved `internal_reference`.
`moving_node_attachment` retains every full polynomial node; `moving_nodes` and
`moving_parameter` recover all eighteen original moving nodes and every point
of their characteristic simplex after the displayed chart and reference maps.
These are equalities before native evaluation. They do not yet glue the full
pre-attachment span surface.

## Composition presentation remains a separate input

This is the actual target carrier for a proposed presentation of the selected
`InputComposition.coneHomotopy f g`; it is not yet that presentation. In particular,
the following are not supplied by carrier contractibility:

- A pre-`beta` scalar lift of the complete original `InputCompositionSpan.homotopy`.
- Its whole scalar attachment to the existing `InputCompositionCarrierTop.face`.
- The original moving-null boundary conversion and cone reassociation in scalar
  coordinates, retaining the already selected comparison cube.
- A stage-two raw Bass composition or an all-stage successor theorem.

The existing global `InputCompositionTopInternalNodes.internal_reference` can be
used in the next polynomial-node attachment proof: reanchor the actual 18-node
polynomial rectangle to `E ≫ projectionMap X` with
`E := InputCompositionTopPieces.baseSource f g`. This is an exact finite source
calculation, not an additional arbitrary-family lifting hypothesis.

For this remaining composition presentation, each original polynomial chart
is `movingSquare.pauseRight`; the terminal constant half of polynomial
composition must be retained. An unpaused cone comparison does not recover the
already selected `InputComposition.coneHomotopy` boundary.

The exact positive-cone restriction is separately constructed in
[GlobalRawBassInputCompositionPositiveFactor](GlobalRawBassInputCompositionPositiveFactor.lean).
It retains this terminal pause and the entire original corrected cone-null square,
and recovers the complete original source rail. See the
[null-composition boundary](RawEvaluation.md#original-null-composition-boundary-and-positive-support).
It does not supply the genuine inverse-polynomial sector, arbitrary overlap
presentation, or the scalar intersections required for a whole selected K presentation.
