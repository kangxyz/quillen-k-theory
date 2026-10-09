# Independent review: weak source change and pasting

## Accepted scope

Accepted after full semantic review, fresh isolated compilation of both
sources, and a warning-free fixed-15 recursive-origin audit with 18 exact
consumers. The terminal audit completed at 09:49:57 UTC on 2026-10-09.
Original source and inspected prerequisite hashes were rechecked unchanged.
The frozen source manifest is `logs/weak-pullback-pasting-sources.sha256`; its
independent copy has fingerprint
`b66b40f9667197dde7e53ab14f552a6412a90c49d9189e804671f8a274e367cb`.

- `Topology/HomotopyPullback/WeakSource.lean`:
  `9b8b08eb277c756d666ae5750c1edea49c3734a6bcff9887d3746bf94a1a67c8`
- `Topology/HomotopyPullback/WeakPasting.lean`:
  `118568445366e7a41189b08b1667f7918407d4842059bf49a8beeb3c1345f116`

Paths above are relative to `Quillen/`. The original sources are unchanged.

## Mathematical and original-map check

The source projection of an actual compact-open-path homotopy pullback is
a genuine Hurewicz fibration: the proof uses the exact path-reversal
homeomorphism to the accepted base projection. No original map is assumed
to be a fibration.

`sourceMapPullbackHomeomorph` identifies the original source-changed
homotopy pullback with the strict pullback of the original weak source map
along that source projection. Both directions are continuous on the actual
subtype/product/path model; the inverse preserves the whole original path.
The genuine weak right-properness theorem then proves the original
`sourceMap` weak. Its parameter and complete path are unchanged, and its
source coordinate is exactly the original source map applied to the old
source. No global inverse family is selected from weak-equivalence data.

The pasting factorization was checked on its complete target subtype. The
canonical outer comparison followed by `pastingIntoNestedEquiv` equals the
original left comparison followed by the original source-change map of the
right comparison. The commutative square accounts for the middle
parameter and the complete inner constant path; the other path is
unchanged. The supporting nested equivalence was read: an actual
strict-pullback homeomorphism followed by strict-to-homotopy-pullback
comparison for the genuine base-projection fibration. Thus it is genuinely
available without either original square being homotopy cartesian.

Weak source change and composition yield the weak composite. Empty-aware
cancellation of the genuine nested equivalence proves weakness of the
original outer canonical comparison. The theorem does not use the older
pasting theorem whose hypotheses require actual comparison equivalences.

## Exact scope

One arbitrary common universe is explicit. The source-change premise is
weakness of the original source map. Pasting needs the two incoming
original comparisons weak. The complete conclusions contain component
surjectivity and bijectivity on every actual finite based homotopy set,
including degree zero. Empty spaces require no added nonemptiness
hypothesis. There is no connectedness, compactness, separation, CW-type or
local-contractibility assumption. Finite pushout/gluing remains separate.

## Independent evidence

The fresh first-`LEAN_PATH` overlay and acquisition/hash/build logs are
`logs/weak-assembly-independent-20261009/`. Both reviewed compiled stems
were excluded before fresh compilation; unchanged prerequisites are
symlinked. Shared slot1 and single-threaded Lean preserve the global cap.

`audits/WeakPullbackPastingIndependentAudit.lean` fixes all 15 defining
origins, including generated homeomorphism proofs, recursively allowing
only `propext`, `Classical.choice` and `Quot.sound`. Its 18 consumers also
import `Quillen.Library`. They test original source/parameter/path formulas,
the inverse homeomorphism's entire path, genuine projection HLP, the full
pasting identity, arbitrary-degree and explicit degree-zero maps, component
surjectivity and empty-source/empty-target consequences.

Script: `logs/verify-weak-assembly-independent.sh`.

Terminal logs: `check.log`, `WeakPullbackPasting-audit.log`,
`WeakPullbackPasting-deps.log`, `WeakPullbackPasting-hashes-after.log`,
and `prerequisites-after.log` in that evidence directory.
Artifact manifest: `logs/weak-assembly-independent-20261009/artifacts.sha256`.
