# Independent review: original mixed evaluation into the coarse S-construction

Accepted 2026-10-09 12:03:14 UTC.

## Frozen sources

The four original sources are `MixedNerves/DiagonalEvaluation`,
`ChainEvaluation`, `CoarseRows`, and `TotalEvaluation`, under
`Quillen/Waldhausen/Fibration`. The exact manifest is
`logs/mixed-evaluation-target-sources.sha256`.
All four complete sources were read. No production source or live build
artifact was changed in this review.

## Mathematical assessment

Diagonal evaluation uses the actual original horizontal coarse arrows
and vertical fine arrows, with nesting proving that their displayed
composite is coarse weak. Restriction along the genuine diagonal functor
is simplicial. The original constant-chain inclusion is a strict section.
Its separately proved homotopy equivalence, together with that strict
section, proves that this prescribed evaluation is a homotopy equivalence.
The forward map is not silently replaced by a chosen inverse.

The literal transpose transports this statement to the original mixed
chain model. The inverse is the original constant section through the
inverse transpose. Compatible-functor naturality is proved using actual
postcomposition and the functor composition law, including the cofibration
chain augmentation.

The coarse row object condition agrees with the unchanged fine row object
condition because cofibrations agree and zero/pushout conditions are
absolute. Explicit inverse views preserve every original diagram and
natural transformation. Their restrictions to actual coarse weak maps are
strict inverses, commute with actual ordinal restriction, and give a
bisimplicial isomorphism. The final target is the original coarse Waldhausen
S-set via the already accepted original-grid nerve presentation.

The final rowwise evaluation is genuinely natural before realization.
The accepted diagonal realization theorem therefore supplies its actual
total equivalence. The cofibration variant composes the separately proved
cylinder-based total inclusion equivalence. Its forward map is exactly
the original total cofibration-chain evaluation into the original coarse
S-construction.

Categorical maps and coarse row/total evaluation retain independent base
object/hom universes. The raw coarse-chain realization uses its explicit
max-universe presentation; arbitrary-scheme consumers verify that scope.
The genuine cofibration-total equivalence retains the existing common
universe (`SmallCategory`) plus coarse two-out-of-three, structural
`JointData`, and the actual second-endpoint-section hypothesis. No desired
realization equivalence, fibration, or natural family of chosen inverses is
assumed. This endpoint does not prove the global fiber/Gillet–Waldhausen
comparison.

## Verification

A separate first-path overlay excluded all four target artifact families,
then compiled every target from its frozen source. All actual imports
resolve to fresh regular target oleans, checked with `lean --deps`.
The independent combined audit recursively checks exactly **111 origins**,
with the fixed per-module split **33 + 20 + 40 + 18**, against only
`propext`, `Classical.choice`, and `Quot.sound`.

All **79 consumers** pass. These retain the 75 authored consumers and add
an original total cofibration-grid object formula, the actual prescribed
coarse map's inverse homotopy, the exact cofibration forward map, and its
full structural-hypothesis equivalence type. The retained consumers cover
original objects/arrows, both strict inverse views, strict reindexing,
actual constant sections, full targets, degree zero, concrete complexes,
and independent-universe scheme coarse evaluation.

Every target hash and all **3,778 prerequisite-source**, **17,355 dependency
artifact**, and toolchain/project-pin hashes are unchanged before/after.
The final source and audit checks are warning/error-free. Initial combined
audit attempts had only namespace-scoping omissions and an incorrect
consumer-only chain identifier; their logs are retained. No source proof
or theorem statement was revised to pass the review.

## Replay and evidence

- Audit: `audits/MixedEvaluationTargetIndependentAudit.lean`
- Preparation: `logs/prepare-mixed-evaluation-target-independent.py`
- Fresh build: `logs/verify-mixed-evaluation-target-independent.sh`
- Final audit replay: `logs/verify-mixed-evaluation-target-independent-final.sh`
- Full directory: `logs/mixed-evaluation-target-independent-20261009/`
- Final driver: `logs/mixed-evaluation-target-independent-final-driver.log`
- Evidence: `logs/mixed-evaluation-target-independent-20261009/artifacts.sha256`
