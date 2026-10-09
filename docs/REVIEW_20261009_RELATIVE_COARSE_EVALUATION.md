# Independent review: original relative-to-coarse assembly

Accepted 2026-10-09 12:08:07 UTC.

## Frozen sources

- `Quillen/Waldhausen/Fibration/RelativeRows/FiberFiltration.lean`
- `Quillen/Waldhausen/Fibration/RelativeRows/CoarseEvaluation.lean`

Manifest: `logs/relative-coarse-evaluation-sources.sha256`.
Both sources were read completely. Their bytes and all live build artifacts
were left untouched. The evaluation4 prerequisite was independently accepted
by the parent before this review was finalized; see
`docs/REVIEW_20261009_MIXED_EVALUATION_TARGET.md`.

## Semantic assessment

The original fiber functor sends every initial interval `[0,i+1]` to the
same original `[0,1]` interval. Its original objects, structural identities,
and arbitrary input morphisms are retained exactly. The equality with the
constant-chain functor is genuinely proved.

`coarseEvaluation` composes the actual original relative-filtration map
with the prescribed mixed evaluation into the original coarse S-set.
Its object formula reads the original initial interval at the same nerve
index. The homotopy equivalence composes the separately established actual
equivalences, and its forward-map theorem identifies the unchanged
simplicial evaluation, not a chosen inverse.

The canonical triangle is an equality of the original simplicial maps:
`totalFiberInclusion ≫ coarseEvaluation = sSetMap (changeWeak_exact N)`.
The proof decomposes the original product-poset grid arrow into interval
and time parts and uses the original functor's composition law. The
realized triangle then follows by genuine realization functoriality.

Zero tracking is exact in every degree. The forward diagrams keep the
original fine zero; `N.zero_eq.symm` identifies it with the actual chosen
coarse zero. Uniqueness of zero morphisms supplies the whole zero-simplex
identity, including all maps. The chosen total relative vertex is the
original all-zero vertex, and the realized basepoints are obtained by its
actual yoneda vertex map. No replacement zero, alternate basepoint, or
new rebasing path is introduced.

The map, canonical triangle, and zero/basepoint assertions require the
structural coarse extension axiom but no cylinder or saturation. The
homotopy-equivalence assertion additionally requires the genuine joint
cylinder, its actual second-endpoint section, and coarse two-out-of-three.
These are structural inputs, not conclusions of the comparison encoded as
assumptions. The two actual bounded-terms consumers discharge all these
inputs from the accepted complex constructions using only the stated
zero/replete/extension-closed term property, without kernel closure.

The helper retains independent object/hom universes; the raw S-realization
assembly explicitly uses the established common-universe API. This proves
the actual relative total model equivalence and canonical based forward
triangle. It is not itself the remaining global homotopy-fiber/fibration
or Gillet-Waldhausen theorem.

## Independent verification

A fresh first-path overlay excluded all target artifact families. Both
frozen targets were rebuilt, and actual import paths were verified against
fresh regular target files. The terminal check and audit are warning-free.

`audits/RelativeCoarseEvaluationIndependentAudit.lean` uses one declaration
traversal, recursively allowing only `propext`, `Classical.choice`, and
`Quot.sound`. The fixed total is **24 = 4 + 20**.

All **25 consumers** pass: the original 18, the genuine bounded-terms
construction and exact-forward consumer, plus five stronger checks of the
arbitrary original grid-arrow triangle, the degree-zero original object,
the literal zero vertex, the evaluated realized triangle, and the original
fiber morphism with independent categorical universes.

All source hashes, **3,815 prerequisite-source hashes**, **17,395 dependency
artifact hashes**, and toolchain/project pins agree before and after.

Two review-harness-only issues were corrected. An added consumer initially
tried `congrArg` into a dependent Hom; the final test proves the original
arrow factorization directly. An audit-only replay omitted the source
import log, so both sources were rechecked. Their artifacts were verified
byte-identical to those used by the successful fixed24 audit. No production
source change was necessary. The initial consumer diagnostic is retained.

## Evidence

- Directory: `logs/relative-coarse-evaluation-independent-20261009/`
- Full replay: `logs/verify-relative-coarse-evaluation-independent.sh`
- Terminal source replay: `logs/recheck-relative-coarse-evaluation-independent-sources.sh`
- Terminal driver: `logs/relative-coarse-evaluation-independent-terminal-driver.log`
- Audit: `audits/RelativeCoarseEvaluationIndependentAudit.lean`
- Full manifest: `logs/relative-coarse-evaluation-independent-20261009/artifacts.sha256`
