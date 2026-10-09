# Independent review: whole boundary-track cover

Date: 2026-10-09. Reviewer: split-complex comparison worker.

## Decision and mathematical scope

`Quillen/Topology/HELP/BoundaryTrackCover.lean` is independently accepted. The source gives the literal open cover controlling every point of the entire original boundary track. Its four spaces retain independent universes.

The only compactness assumption for closedness is `CompactSpace A`, where `A` is the boundary source. The parameter `D` is assumed Hausdorff, with no compactness or local compactness requirement. The boundary map is merely continuous; no injectivity, embedding, or HEP is used. The target and base need no separation assumptions.

The exact all-time base equality and the complement-fiber hypothesis are retained. No endpoint-only inference, lifting result, arbitrary-closed-subset HEP, mixed attachment theorem, or global gluing theorem is asserted.

## Semantic review

The entire production source and its fourteen authored consumers were read.

The bad set is exactly the image of `H⁻¹(Nᶜ)` under `(t,a) ↦ i(a)`. Openness of `N` makes this preimage closed in the compact product of the actual time interval and `A`. Its continuous image is compact and hence closed in the Hausdorff parameter space `D`. Neither the proof nor its type assumes `D` compact.

The first chart is exactly `b⁻¹(N) \ bad`; the second is exactly `(q ∘ b)⁻¹(V)`. The first is open by the proved bad-set closedness and the second by continuity. A parameter outside the second chart has its target in `N` by the complement-fiber hypothesis. If a bad point lay over that parameter, the displayed equality at that same time and boundary point would force its track value into `N`, contradicting badness. This proves the exact cover and the containment of all bad parameters in the second chart.

For the first chart, whole-track containment follows directly by ruling out the corresponding bad-set witness at each original time. For the second chart, the supplied all-time base equation proves containment in `q⁻¹(V)` at every time. The proofs apply to every boundary point over a parameter, even when the boundary map has multiple preimages.

## Independent validation

Final replay: warning-free exit 0 at 14:35:05 UTC, with a fresh source, all 13 origins, all 19 consumers and all prerequisite hashes passing without repairs.

- Fresh target build with the entire old compiled family excluded from the first-path overlay; the audit's actual import resolves to that fresh artifact.
- All thirteen source-origin declarations recursively audited using a fixed count, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
- Nineteen consumers: the author's fourteen plus the exact all-preimages/all-times characterization of the first chart, a constant boundary map with no injectivity, an arbitrary-time bad witness landing in the second chart, a genuinely noncompact real parameter, and the actual empty zero-cube boundary giving an empty bad set.
- Full audit-import source and compiled-artifact manifests explicitly seed implicit `Init`; all prerequisite hashes, actual Lean/Lake binaries and project/toolchain pins are checked before and after the replay.
- No production source, live compiled artifact, or held public umbrella was edited.

Prerequisite totals: 3,485 sources and 16,066 compiled artifacts.

## Evidence

Frozen source manifest: `logs/boundary-track-cover-sources.sha256`, SHA-256 `7fa51e274d64480f4c1b15c409bf7f9716c51928d8ee020f2b41443c0a09e825`.

Independent audit: `audits/BoundaryTrackCoverIndependentAudit.lean`.

Evidence directory: `logs/boundary-track-cover-independent-20261009/`.

Driver: `logs/boundary-track-cover-independent-driver.log`.

Preparation/check scripts: `logs/prepare-boundary-track-cover-independent.py` and `logs/verify-boundary-track-cover-independent.sh`.
