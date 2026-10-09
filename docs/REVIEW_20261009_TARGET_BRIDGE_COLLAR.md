# Independent review: actual target-end bridge collar

Date: 2026-10-09. Reviewer: split-complex comparison worker.

## Decision and scope

The two frozen sources `MappingCylinderTargetCollar.lean` and `FiberwiseBridgeTargetCollar.lean` are independently accepted. They construct the actual open positive-height target collar and its genuine fiberwise strong deformation retraction onto the original target inclusion. The displayed arbitrary common categorical universe is retained.

No weak equivalence, homotopy equivalence, lifting property, compactness, separation, or injectivity of either attaching map is assumed. In the normalized wrappers the input `NormalizedFibrationSpan.Data` consists only of the displayed spaces, maps and over-base equality; stronger results elsewhere in that imported module are not used as hypotheses or conclusions here.

## Semantic review

All 325 production lines were read, together with the actual target-cylinder deformation, the SDR interface, the open-pushout descent and the normalized data definitions.

The mapping-cylinder height is the genuine pushout descendant of cylinder time and the constant value one on the target. It is zero at the source endpoint. The proof evaluates the original target deformation on both original pushout legs; its height is exactly the displayed interval slide. This implies that every point in the strict superlevel collar remains in that same collar throughout the deformation. The SDR is therefore the literal restriction of the existing deformation, with the original target inclusion and original projection retraction.

For the bridge, the height is the genuine pushout descendant of the left height and the constant zero map on the entire right cylinder. Agreement holds at the actual source seam. Thus height is exactly one at the original left target `Q0` and exactly zero on every point of the opposite cylinder, not merely at its endpoints.

Each cut lies in the unit interval. Its strict superlevel set is open, and the opposite corner has empty preimage since its height is zero. The auxiliary open-pushout chart constructs actual mutually inverse continuous maps using the genuine restricted pushout descendant and its uniqueness. This gives the literal collar homeomorphism, with forward coordinate equal to the original left bridge leg. The transported SDR retains the original `Q0` inclusion, fixes that target at every time, and is fiberwise over the unchanged bridge projection.

The homotopy convention is explicit: at time zero it is target-after-retraction, and at time one it is the identity. The entire deformation stays over the original base. At cut one the collar is empty; the SDR endpoint requires the displayed strict condition `cut < 1`.

## Independent validation

Final replay: warning-free exit 0 at 14:46:13 UTC, with both fresh sources, the fixed 94-origin audit, all 36 consumers and all prerequisite hashes passing.

The recursive defining-origin audit fixes all 94 original declarations with module counts `[37, 57]` and permits only `propext`, `Classical.choice`, and `Quot.sound`. All 36 consumers comprise the author's 27 plus nine independent checks of the exact lifted height value, both SDR endpoints, fixed target points for all times, the entire opposite-cylinder exclusion, cut-one emptiness, pointwise full-time fiber preservation, the original normalized inclusion, and the original bridge-leg formula for the inverse collar coordinate.

Both old target compiled families are excluded from the first-path overlay before rebuilding in order. The audit's actual target imports are verified to be fresh. Full audit-import provenance seeds implicit `Init`; prerequisite source/artifact hashes and actual toolchain/project pins are checked before and after the run. No frozen source, live compiled artifact, or public umbrella is edited.

Prerequisite totals: 3,871 sources and 18,250 compiled artifacts.

The first fresh pair and fixed-94 recursive audit passed, but the added pointwise normalized-base consumer reached the default definitional-unfolding heartbeat limit. The independent driver was repaired with the source's existing transparency settings and an explicitly inferred intermediate equality. No source proof, hypothesis, or heartbeat limit was changed. The initial driver, logs and fresh artifacts are retained; all production/prerequisite manifests are identical across both runs.

## Evidence

Source manifest: `logs/target-bridge-collar-sources.sha256`, SHA-256 `cfac84c06a08adccf6bd39a696068ff4adc1aab70aac968bcc2df2d018e314ab`.

Independent audit: `audits/TargetBridgeCollarIndependentAudit.lean`.

Evidence directory: `logs/target-bridge-collar-independent-20261009/`.

Driver: `logs/target-bridge-collar-independent-driver.log`.

Preparation/check scripts: `logs/prepare-target-bridge-collar-independent.py`, `logs/verify-target-bridge-collar-independent.sh`.
