# Independent review: original relative rows and weak chains

## Boundary and semantic review

Reviewed unchanged sources:

- `Quillen/Waldhausen/Fibration/RelativeRows/WeakChains.lean`
- `Quillen/Waldhausen/Fibration/RelativeRows/FiltrationWeakMaps.lean`

The exact source manifest is
`logs/relative-weak-chains-independent/sources.sha256`, copied from the author's
frozen source manifest. Full semantic read found no issue.

`WeakChains` changes only the actual zero corner of the existing quotient
pushout to the chosen coarse zero, by an actual zero-object isomorphism.
Its coarse-weak/coarse-acyclic equivalence uses the accepted structural
extension axiom and the original displayed cofiber square. The original
initial filtration retains precisely the intervals `[0,i+1]` and their
original interval maps. Its fine cofibration proof is the original row's
horizontal cofibration proof. The relative-row object predicate is exactly
coarse weakness of every original initial-filtration arrow.

`FiltrationWeakMaps` packages this same original filtration in the existing
`ComposableArrows C n.len` category, retaining all natural transformations.
The omitted initial zero vertex is handled by its actual zero-object
isomorphism. Given fine weakness on the retained initial objects, genuine
Waldhausen gluing on the original quotient squares proves fine weakness on
every quotient component. No extension or saturation hypothesis is used
for this fine-map detection. The strict ordinal-reindexing equality follows
from the original added-vertex ordinal functor and unchanged diagrams.

Neither module assumes or concludes a presentation equivalence, cylinder
comparison, realization equivalence, or fibration theorem. Object and
morphism universes remain independent. Outer degree zero is included.

## Independent verification

The script `logs/relative-weak-chains-independent/verify.sh` creates a fresh
project overlay, initially excluding every compiled-artifact family of both
targets. All other dependencies are linked to their accepted artifacts. The
original live project artifact path is replaced by this excluded-target
overlay. Both targets are rebuilt
in source order; the second source and audit consume only the fresh target
artifacts. The live accepted artifacts are not changed.

`audits/RelativeRowsWeakChainsIndependentAudit.lean` retains the fixed22
source-origin guard and recursively checks all dependency axioms against
`propext`, `Classical.choice`, and `Quot.sound`. It includes the author's13
consumers plus5 independently added consumers for the literal positive
interval arrows, outer-degree-zero fine detection without coarse extension,
the omitted zero diagonal, the same-arrow fine/coarse assertion, and the
actual chosen-zero cofiber square. Both source manifests are rehashed before
and after verification.

**Accepted.** Both fresh source builds, the final fixed22 recursive origin
audit, all18 consumers, exact fresh import paths, and all source hashes passed
without warnings, errors, or `sorryAx`. Only the standard three axioms occur.
The complete32-module Quillen source closure and its used artifact hashes
are retained alongside the target hashes.

The first verification attempt stopped on a search-path-layout error before
source elaboration: Lean resolves a package prefix from a single directory,
so a separate sparse first overlay cannot fall back to another Quillen
package directory. The rerun uses a single excluded-target project overlay;
no implementation source was changed.

An additional degree-zero consumer needed explicit reduction of the zero
finite index before its elementary arithmetic proof. This was confined to
the independent audit driver; the final driver and raw log are clean, and
both implementation source hashes stayed unchanged.
