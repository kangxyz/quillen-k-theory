# Independent review: finite cube HELP from weak equivalences

Date: 2026-10-09. Reviewer: split-complex comparison worker.

## Decision and exact scope

The four sources listed in `logs/weak-finite-help-sources.sha256` are independently accepted after complete semantic review and an excluded-target fresh rebuild. The original weak homotopy equivalence supplies full prescribed-boundary HELP on every literal finite cube-boundary pair, including dimension zero. Consequently the original mapping-path endpoint has `CubicalSubdivision.BoundaryLifting`.

The main endpoint is `Quillen.IsWeakHomotopyEquivalence.cube_fullHELP`. It retains the original boundary map and its entire prescribed homotopy at every time. `mappingPath_endpoint_boundaryLifting` retains both the source coordinate and the entire stored boundary path. The ambient topological universe is explicitly common. No CW-type assumption, full arbitrary compact-pair HELP, homotopy inverse, or global Waldhausen fiber conclusion is asserted.

## Semantic review

All 599 production lines were read, together with relevant accepted pullback, pair-lifting, stationary-lifting and boundary-duration prerequisites.

- `WeakFiniteBased`: actual cubical homotopy-set surjectivity gives constant-boundary strict HELP; genuine HEP and boundary unpadding restore the original prescribed homotopy. The empty boundary in dimension zero uses component surjectivity without an externally supplied source point.
- `CubicalHorn`: the horn is literally the side faces and bottom face. The top cube and horn cover the entire product boundary by a compact-Hausdorff quotient. The displayed rim agreement yields genuine descent and a genuine pushout, hence horn HEP by cobase change. The next-cube boundary homeomorphism retains the displayed coordinates. In dimension zero the horn is the bottom point and the rim is empty.
- `WeakCubeFilling`: genuine horn HEP normalizes the original boundary map; the top face is then an actual generalized loop. Its singleton based homotopy set provides a relative nullhomotopy. Whole-boundary HEP restores the exact original boundary map. The zero-dimensional cube case uses explicit nonemptiness rather than a vacuous based condition.
- `WeakFinite`: the actual homotopy pullback over the test cube is weakly contractible by the accepted original weak-map base-change theorem. Its boundary point stores the original source map and full prescribed path. After extending it, actual straight interpolation and stationary lifting with the proved boundary-duration zero locus correct the parameter while fixing the whole boundary point. Pair lifting converts this into the original mapping-path endpoint RLP.

No new axioms, `sorry`, replacement weak-equivalence assumptions, or unproved lifting conclusions were found.

## Independent validation

The single-pass audit `audits/WeakFiniteHELPIndependentAudit.lean` checks all 87 defining-origin declarations, with fixed module counts `[4, 66, 2, 15]`. Every recursively collected axiom is among `propext`, `Classical.choice`, and `Quot.sound`.

The 32 consumers include the author's 24 original-map tests and eight independent tests: literal zero-dimensional horn and whole boundary; the actual empty-rim pushout; both original descent restrictions; product-boundary filling from singleton pi-zero without an external source point; all-dimensional mapping-path source and whole-path recovery; and nonconstant one-dimensional prescribed-boundary HELP.

The four target compiled families are excluded from the first-path overlay before rebuilding. The final audit resolves each target to its fresh overlay artifact. Frozen production hashes, full audit-import prerequisite source and compiled artifact hashes, actual Lean/Lake binaries and project/toolchain pins are rechecked before and after the replay. No production or live compiled artifact was changed.

## Provenance expansion

The first fresh-four/fixed-87/32-consumer replay passed warning-free at 14:14:22 UTC. During review, the explicit-import scanner was found to omit Lean's implicit `Init` import. This was a provenance-coverage gap, not a production proof defect. The entire initial successful evidence directory and driver log were preserved before expansion.

The corrected scanner explicitly seeds the pinned toolchain's `Init.lean` and compiled family, then recursively follows its imports. The source manifest grew from 3,388 to 3,544 prerequisites, and the compiled-artifact manifest from 15,722 to 16,190: exactly 156 source and 468 artifact additions, with no removals and all previous hashes identical. Exact added paths and hashes are retained in `added-sources.{txt,sha256}` and `added-artifacts.{txt,sha256}`. The expanded manifest was used for a separate fresh replay, not merely rehashed after the earlier check.

Final expanded replay: warning-free exit 0 at 14:20:31 UTC, with all four fresh sources, fixed 87 origins, 32 consumers and all expanded prerequisite hashes passing.

## Evidence

- Frozen source manifest: `logs/weak-finite-help-sources.sha256`, SHA-256 `5f1d0a16fe3713a0ae90777453ab7f54694e92e164cc2ab8db72c94cf2f93d14`.
- Independent audit: `audits/WeakFiniteHELPIndependentAudit.lean`.
- Final expanded evidence: `logs/weak-finite-help-independent-20261009/`.
- Final driver: `logs/weak-finite-help-independent-driver.log`.
- Preserved initial evidence: `logs/weak-finite-help-independent-initial-explicit-20261009/`.
- Preserved initial driver: `logs/weak-finite-help-independent-initial-explicit-driver.log`.
- Reproducible preparation/check scripts: `logs/prepare-weak-finite-help-independent.py`, `logs/verify-weak-finite-help-independent.sh`.
