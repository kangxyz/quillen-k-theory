# Independent review: stable Q/S rows, flags and map models

Date: 2026-10-09 (UTC).

## Scope

The exact 26-source scope is recorded in
`logs/review-20261009-qs-stable-sources.sha256`; the dependency-ordered module
list is `logs/review-20261009-qs-stable-modules.txt`.
It is the local `Quillen.Waldhausen.QuillenComparison` dependency closure of
`RowFull`, `FlagPresentation`, `MixedNerve`, `ChainClassification`,
`BisimplicialMap`, `RowDiagonal` and `ComparisonHom`.

This review does not cover the actively developed `PullbackQuotients` or
`Factorization` modules, nor the separately owned `FlagPullback` and
`FlagExtension` construction. No implementation source was changed.

## Semantic findings

- Exact rectangles use the original S-pushout to prove its cokernel universal
  property, and exactness identifies the genuine conflation. The overlap
  pullbacks then prove composition of the actual admissible Q-span representatives.
- Faithfulness is genuine: monic maps into the whole interval determine initial
  components, and epic quotient maps determine the remaining components.
  The last central interval is the whole row, and injectivity of the original
  isomorphism-to-Q-isomorphism map detects equality there.
- Fullness uses the proved bijection between original and Q-isomorphisms.
  Naturality to the final Q-object lifts to an actual span-apex isomorphism.
  The upper initial subobject is that apex; the lower one is its actual kernel.
  Covering all endpoints reconstructs compatible initial subobjects. Cokernel
  extension recovers the whole row, and epic cancellation checks each originally
  prescribed central quotient component. Essential surjectivity is not an input.
- Admissible-flag completion uses actual categorical cokernels of the original
  inflations. The quotient inclusions are pushouts of inflations, and successive
  quotients satisfy the cokernel universal property needed for S-pushouts.
  Diagonal quotients are zero because they are cokernels of identities. Natural
  maps and isomorphisms of completed flags are induced by cokernel maps.
- `completedInitialIso` is the genuine uniqueness isomorphism between two
  cokernels of each initial-flag map. Conversely, a zero-start flag is recovered
  by its canonical quotient isomorphisms. Neither conclusion is assumed.
- Both row-diagonal and classification-diagonal identifications are actual
  inverse simplicial maps, reconstructing every grid map from row/column maps.
  `rowChainNerveMap` is strictly simplicially natural on both objects and
  component isomorphisms; no compatible choice of reconstruction is assumed.
- `MixedNerve` permits distinct hom universes while requiring the two categories
  to inhabit the same common object universe `max u v w`. Postcomposition gives
  the exact nerve map, and natural transformations give explicit interval
  cylinders. Unit and counit isomorphisms provide the two realized homotopies.
  This is a same-realization-universe argument, not a cross-universe assertion.
- The based map retains the specified zero vertex. `comparisonK` only inverts
  the independently proved edgewise endpoint group isomorphism. Its zigzag
  characterization and uniqueness are proved; Q/S equivalence is not claimed.

The supporting `QConstruction.Core` argument was also read: invertibility of a
Q-span forces both legs invertible, using admissibility and an actual splitting,
not an unproved balancedness principle.

## Verification

- All 26 implementation sources were rebuilt from the exact recorded hashes,
  in dependency order, with matching output oleans. The manifest matched before
  and after rebuilding. Each Lean process held compiler slot 2.
- All 465 declarations originating in these modules, including generated and
  private declarations, passed recursive axiom collection. Only `propext`,
  `Classical.choice` and `Quot.sound` occurred. The audit was then count-frozen
  at 465 and rechecked.
- Arbitrary-universe external consumers passed for row fullness/faithfulness,
  actual flag completion and presentation, both diagonal isomorphisms, the
  bisimplicial map and its exact degreewise formula, mixed-hom-universe realized
  nerve equivalence and its exact forward map, both chosen basepoints, and the
  comparison-group map's exact zigzag identity.
- The focused source rebuild produced 14 pre-existing non-failing linter
  warnings about unused section variables and `letI` style. There were no source
  errors. The all-origin audit and consumer examples produced no warnings or
  errors. No implementation source was changed to silence lint.
- Verification artifacts: `audits/Review20261009QSStableAudit.lean`,
  `logs/review-20261009-qs-stable-check.sh`,
  `logs/review-20261009-qs-stable-check.log`, and
  `logs/review-20261009-qs-stable-audit.log`.

Result: accepted within the exact stable scope above.

## Boundary

Acceptance of these stable modules proves the actual canonical comparison map,
fullness and faithfulness in each row, and genuine flag completion. It does not
prove row essential surjectivity, the resulting Q/S realization equivalence,
Gillet–Waldhausen, or a comparison equivalence with PerfectK.
