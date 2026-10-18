# The standard original completion comparison

The public completion-to-Q-loop comparison has the standard sign. A stage
`(n, P)` has class `[P] - [R^n]`. The Q-construction, positive object generators,
K-groups, canonical exact-functor K-maps, algebraic completion grades and
loop-degree shifts retain their definitions. The specified map and track below
give the normalization.

## The actual map and track

`completionToOriginalQLoops R U` reflects exactly the inner loop coordinate
after the original generic loop/fiber inverse and source-to-fiber comparison.
`originalQComparison` uses this map at the unchanged additive zero pair.
`completionToOriginalQLoops_eq_reversal_fiberInverse` gives the exact relation
to the unchanged generic inverse.

The prescribed track has value `q_fiber(s)(1 - t)` at outer path parameter `s`
and inner loop parameter `t`. Here `q_fiber` is the specified loop-valued
basepoint track of the unchanged generic loop/fiber inverse at the original
fiber point. The outer path direction is retained. The generic
`originalQLoopFiberHomotopyEquiv`, its inverse homotopies and the original
source-to-Q-zero fiber path keep their definitions.

The reflection interface reuses `Quillen.loopReversalHomeomorph` from
`Quillen.Topology.HomotopyGroups.Loop.LeftComponentTranslation`, with its
explicit basepoint. There is no second reversal in the standard map.

## Component labels and positive degrees

At a displayed basepoint `U`, the component label is the input completion grade
minus `completionKZeroClass U`. Thus the actual additive zero pair and standard
zero stage give numerator minus denominator. At stage `(n, P)`, the class is
`[P] - [rankOnePower n]`, meaning `[P] - [R^n]`. The nonzero-grade basepoint
contributes its displayed subtraction. These are virtual projective classes;
no numerical-rank classification or invariant-basis-number hypothesis is used.

`completionPositiveKEquiv R U n` and its exact zero-component counterpart use
the original loop-degree shift and transport along the prescribed track.
Their index `n = 0` is K₁ and `n = 1` is K₂. Reflection of one cube coordinate
induces homotopy-group inversion in every positive degree, without a
dimension-parity factor. Generic reversal reverses concatenation order;
inversion is used as a group map only in the already commutative K targets.

## Current clients

Use `Quillen.KTheory.Plus` for the standard comparison, exact equivalences,
naturality homotopies, positive comparisons and component labels.

The [normalization client](../../../examples/downstream/Consumer/StandardSignMigration.lean)
checks the standard stage labels and component classifiers. The
[map and track tests](../../../QuillenTest/ProjectiveCompletionLoops.lean) and
[positive naturality tests](../../../QuillenTest/ProjectiveCompletionPositiveKNaturalityCore.lean)
check the corresponding public formulas. The
[label client](../../../examples/downstream/Consumer/OriginalCompletionLoopLabels.lean)
and [label tests](../../../QuillenTest/OriginalCompletionLoopLabels.lean) retain
arbitrary basepoints, the zero ring and noncommutative matrix rings. The
[reflection client](../../../examples/downstream/Consumer/LoopReversal.lean)
checks the literal coordinate formula and independent-universe naturality.

## Exact comparisons and ordinary naturality

The original completion-to-Q homotopy equivalence retains exactly the standard
forward map and full prescribed track, including the restriction to actual
zero components. The product uses discrete original K₀ and the specific
original plus-certified `StableCompletion.ZeroComponent R`. Its neutral slice
is the standard zero-component comparison, and its first inverse coordinate
is the original continuous K₀ classifier. Off the neutral slice its forward
map right-concatenates the zero-component loop with the selected representative.

Ambient, zero-component and product forward-map naturality use ordinary
homotopies under common-universe ring change. Their unit-evaluation tracks are
not identified with the separately prescribed comparison tracks. A natural
chosen inverse, strict pointedness, H-space, A∞ or infinite-loop splitting is
not supplied. See [ring plus comparison](README.md) for
the actual maps and [classical CW comparisons](../../Topology/PlusConstruction/ClassicalCW.md)
for the separate actual-CW and coefficient-universe hypotheses.
