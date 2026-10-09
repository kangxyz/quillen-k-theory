# Independent review: compact-parameter lifting corrections

Accepted 2026-10-09 13:03:30 UTC.

## Frozen scope

The five sources under `Quillen/Topology/HomotopyLifting/Compact/` are
`Stationary`, `ParallelLifts`, `OverBaseCorrection`, `FiberwiseExtension` and
`FiberwiseBoundaryCorrection`. Ordered manifest:
`logs/compact-lifting-corrections-sources.sha256`.

All five sources were read completely, including comparison with the full-HLP
proofs they reuse. No production source or live artifact is modified. The
five corresponding original full-HLP source hashes are additionally pinned.
This is after the immutable 12:10 archive freeze.

## Semantic review

`CompactHomotopyLiftingProperty` quantifies only over actual compact, locally
compact parameter spaces in the stated common universe. The data and conclusion
retain the original initial map and full base homotopy. Full HLP genuinely
implies this restricted property. No converse, global mapping-path lifting or
continuous family of inverse maps is asserted.

Stationary correction uses the accepted continuous accelerated base homotopy,
lifts it on the original parameter space, and evaluates at the original time
multiplied by the displayed duration. It keeps the exact original base track
and fixes every duration-zero point throughout. The terminal correction keeps
both the actual source values on that zero set and the exact desired base map.

Parallel correction invokes compact lifting on `I × X`. Its duration
`t(1−t)d(x)` vanishes at both endpoints and on the complete prescribed zero
set. Each case is checked directly. The vertical endpoint comparison and the
entire two-parameter backtrack coherence are retained, with their original
projection formula, endpoint maps and zero-set values. Ordinary comparison
correction first corrects the source using `p`, then uses these actual parallel
lifts for `q`; it does not presume an ordinary homotopy was already vertical.

Fiberwise extension first uses actual HEP to extend the original boundary
track. It then lifts a reversal of the projected time coordinate, with
parameter `I × D` and duration `t d(x)`. This keeps the initial map and every
original boundary value while making the projection exactly stationary over
the original base map.

Boundary correction uses the genuine interval-square HEP extension. The
only compact lifting parameter is `(D × I) × I`. Its duration
`s t(1−t)d(x)` fixes the initial square, both path endpoints and the whole
prescribed boundary. The reversal of the square parameter corrects the base
without changing any of those original data. The final track equals the
supplied boundary track at every time. The unpadding companion constructs the
actual `delayReflLeft` comparison, verifies its endpoints and base formula,
and applies this correction; the needed comparison is constructed rather
than assumed as the desired conclusion.

All lifting calls use `X`, `I × X`, `I × D` or `(D × I) × I`. Their compact
and locally compact structures really follow from the explicit original
parameter hypotheses and the interval's structures. The extension/boundary
source `A` needs no compactness: it is used by HEP, never as a compact lifting
parameter. The duration-zero-locus equation and actual HEP remain explicit.
No positive-dimensional, nonempty-space or separation assumptions are added.

## Independent checks

The first-path overlay excludes every target artifact family and rebuilds
all five frozen sources in order. One module-origin scan checks fixed
**16 = 4 + 5 + 1 + 1 + 5**, recursively allowing only `propext`,
`Classical.choice` and `Quot.sound`.

The **25 consumers** retain all fourteen author tests, including the exact
parallel coherence, ordinary comparison, extension, correction, unpadding and
zero-dimensional cube duration. Added consumers verify compact/locally compact
instances for every actual product parameter, perform literal lifts on those
products using only CompactHLP, expose the exact restricted definition, and
test zero and unit durations without strengthening the input to full HLP.

Audit: `audits/CompactLiftingCorrectionsIndependentAudit.lean`.
Replay: `logs/verify-compact-lifting-corrections-independent.sh`.
Evidence directory: `logs/compact-lifting-corrections-independent-20261009/`.

## Scope remaining

These are actual compact-parameter correction tools. They do not construct
compact lifting for the later collar/cylinder models, prove an arbitrary-space
HLP property, or complete global weak-cartesian/Waldhausen fibration gluing.
Those applications must supply the genuine restricted lifting hypotheses.

## Terminal evidence

All five source rebuilds and the fixed16/all25 consumer audit passed warning-free.
No source or consumer repair was needed. The five target source hashes,
**3,356 prerequisite-source hashes**, **15,660 dependency-artifact hashes**,
project/toolchain pins and the five original full-HLP source hashes agree
before and after. All targets are regular fresh artifacts and actual first-path
import resolution is recorded.

- Terminal driver: `logs/compact-lifting-corrections-independent-driver.log`
- Source/import log: `logs/compact-lifting-corrections-independent-20261009/check.log`
- Audit log: `logs/compact-lifting-corrections-independent-20261009/audit.log`
- Evidence manifest: `logs/compact-lifting-corrections-independent-20261009/artifacts.sha256`
