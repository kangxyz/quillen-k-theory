# Independent review: the original acyclic-to-relative diagram

Accepted 2026-10-09 12:55:24 UTC.

The complete source `Waldhausen/Fibration/AllWeak/RelativeInclusion` was
read under `Quillen`, against the exact frozen manifest
`logs/all-weak-relative-inclusion-sources.sha256`.

## Semantics

The functor applies the actual acyclic inclusion to every original
one-longer quotient-row object and morphism. Its relative-tail witness
comes directly from each source component's acyclicity. Fine exactness
uses genuine exact postcomposition and reflection by the actual fully
faithful forgetful functor. There is no extension or saturation assumption
in the categorical construction, ordinal naturality, chosen zero, or
original split-fiber and tail squares.

The split-fiber square uses an equality of the actual finite
zero/object/zero oneChain, then its original oneEmbedding and ordinal
reindexing. Both S directions retain the original exact-map functor.
All-degree zero simplices and the actual realized total basepoint are
preserved literally. The coarse-evaluation square retains both original
forward maps and only the existing coarse extension and two-out-of-three
inputs required for those exact endpoints. No canonical nullhomotopy
compatibility, global fiber theorem, or fiber-exchange equivalence is
assumed or concluded. Independent object/hom universes survive in the
categorical part; the simplicial part explicitly uses common-universe
SmallCategory, matching its existing map API.

## Verification

A separate first-path overlay excludes the target artifact family and
rebuilds the unchanged source; `lean --deps` verifies the regular fresh
target import. The recursive audit checks exactly **23 source origins**
and **22 consumers**, including the 16 original categorical, simplicial,
zero/basepoint and arbitrary-scheme cases. Six additional checks retain
exact forgetting, oneChain, oneEmbedding, realized split-fiber square,
full diagonal tail square and realized coarse-evaluation square.

The initial audit identified only two review-harness issues: a repeated
universe declaration and a redundant `change` tactic. Both were removed
from the audit. No production source was changed; initial logs are kept. The final replay
passed warning-free. All target, 3,838 prerequisite-source, 17,418 artifact
and toolchain/project-pin hashes matched before and after.

- Audit: `audits/AllWeakRelativeInclusionIndependentAudit.lean`
- Preparation: `logs/prepare-all-weak-relative-inclusion-independent.py`
- Initial replay: `logs/verify-all-weak-relative-inclusion-independent.sh`
- Audit-only replay: `logs/verify-all-weak-relative-inclusion-independent-final.sh`
- Evidence directory: `logs/all-weak-relative-inclusion-independent-20261009`

This source is outside the frozen 12:10 checkpoint.
