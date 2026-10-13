# Standard comparison normalization

The 0.7.0 source integration directly refactors the public completion-to-Q-loop
comparison to the standard sign. A stage `(n, P)` has class `[P] - [R^n]`.
The Q-construction, positive object generators, K-groups, canonical exact-functor
K-maps, algebraic completion grades and loop-degree shifts retain their
definitions. This change affects the comparison map and its prescribed track.
The [0.5.0 owner migration](API.md#migration-to-050) remains applicable.

The package version describes source integration and does not identify a
published tag. Lean remains 4.34.1 and the dependency pins are unchanged.
[Scope](Scope.md#verification) records current merged verification.

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

## Client changes

Use `Quillen.KTheory.Plus` for the standard comparison, exact homotopy
equivalences, actual ambient and zero-component naturality homotopies, positive
comparisons and stage labels. Replace a definitional equality to the generic
loop/fiber inverse with `completionToOriginalQLoops_eq_reversal_fiberInverse`.
When selecting a stage for a K₀ class, use the requested class itself with the
standard stage label; remove the former inversion compensation.

The [normalization client](../../examples/downstream/Consumer/StandardSignMigration.lean)
checks the standard stage labels and component classifiers. The
[map and track tests](../../QuillenTest/ProjectiveCompletionLoops.lean) and
[positive naturality tests](../../QuillenTest/ProjectiveCompletionPositiveKNaturalityCore.lean)
check the corresponding public formulas. The
[label client](../../examples/downstream/Consumer/OriginalCompletionLoopLabels.lean)
and [label tests](../../QuillenTest/OriginalCompletionLoopLabels.lean) retain
arbitrary basepoints, the zero ring and noncommutative matrix rings. The
[reflection client](../../examples/downstream/Consumer/LoopReversal.lean)
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
not supplied. See [ring plus comparison](../topics/PlusConstruction.md) for
the actual maps and [classical CW comparisons](../topics/ClassicalCWPlus.md)
for the separate actual-CW and coefficient-universe hypotheses.
