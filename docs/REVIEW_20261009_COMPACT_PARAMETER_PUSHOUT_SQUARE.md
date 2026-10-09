# Independent review: actual matched pushout squares

Date: 2026-10-09. Reviewer: split-complex comparison worker.

## Decision and exact hypotheses

`Quillen/Topology/Pushout/CompactParameterSquare.lean` is independently accepted. The theorem `Quillen.CompactParameterPushout.isPushout` constructs a genuine pushout on the literal matched subspaces of the original four corners paired with a parameter `D`. Every new leg applies its original leg to the first coordinate and leaves the parameter unchanged.

The primitive theorem assumes only the displayed original pushout, continuous matching maps, a locally compact parameter, and the explicitly closed matching locus in `P × D`. It requires no compactness of `D`, injectivity of either attachment, cofibration condition, nonempty target, or separation condition on the cocone target. The topological categorical objects and parameter share the displayed arbitrary universe.

Separate closed-graph, actual simplicial realization, and actual displayed double-cylinder corollaries discharge the matching-locus hypothesis. The last two retain explicit compactness and local compactness of the test parameter. This does not establish arbitrary pullback preservation of topological pushouts, weak-equivalence preservation, compact HELP, or the eventual mixed open/closed gluing theorem.

## Semantic review

The complete 226-line source and the relevant accepted `CompactParameter`, `CompactParameterQuotient`, `SumSubtype`, `CompactGraph`, and `DoubleCylinderCompactGraph` proofs were inspected.

- The source, left, right, and vertex objects are exactly the stated matching subtypes. The right incoming leg uses the original commuting square only to transport its matching proof.
- The actual sum of the matched outgoing legs is a quotient. This is deduced from the original pushout sum quotient, product with the locally compact parameter, restriction to the explicitly closed target locus, and the literal sum/subtype distribution. The quotient proof uses `IsQuotientMap.of_comp` with continuous factors, with no unproved bijection or general pullback preservation.
- The descendant first uses the genuine underlying set pushout with values in `Option Z`. Matching representatives yield `some` values; nonmatching points yield `none`. Compatibility uses the original commuting equation and the original matched cocone equation. Every matched vertex admits an original pushout representative, so its descendant value exists even for an empty `Z`; no default element is assumed.
- The two exact descendant restrictions and the proved quotient topology yield continuity into an arbitrary target. Joint surjectivity proves uniqueness. These data construct an actual colimit cocone and hence the exact claimed pushout.
- The realization corollaries use proved compact-map closed graphs and the genuine displayed double-cylinder homeomorphism. They do not substitute a homotopy-equivalent base or assume unrestricted separation properties.

`SumSubtype` was independently accepted in the separate nine-source cylinder batch at 14:24:14 UTC before this review. No prerequisite or target production file was edited.

## Fresh validation

Final replay: warning-free exit 0 at 14:30:56 UTC, with the fresh source, fixed 48 origins, all 27 consumers and all prerequisite hashes passing.

The independent audit fixes all 48 source-origin declarations and recursively permits only `propext`, `Classical.choice`, and `Quot.sound`. Its 27 consumers include all 20 author tests and seven extra tests of the original transported matching equation, exact pointwise descendants, empty parameter and empty arbitrary cocone target, the descendant of the literal parameter projections, and a noncompact real parameter with only the supplied closed matching locus.

The target compiled family was excluded before the fresh first-path build, and the audit's import path was verified. Full audit-import provenance explicitly seeds implicit `Init`: 3,545 prerequisite sources and 16,340 compiled artifacts, plus actual Lean/Lake binaries and project/toolchain pins, are rechecked before and after the replay. The original source hash remains unchanged. No live compiled artifact or public umbrella was edited.

The initial fresh source and fixed-48 audit succeeded, but the added real-parameter consumer lacked an inferred `LocallyCompactSpace (ULift ℝ)` instance. This audit-only instance is now genuinely transported along `Homeomorph.ulift`; the initial log and artifacts are retained separately. A second replay elaborated every proof and consumer, but the proof-style linter requested `let` instead of `letI` for that derived instance; the final audit uses the recommended typed `let`, and the warning pass is retained too. All original source, prerequisite and toolchain manifests are byte-for-byte unchanged across all three runs.

## Evidence

- Frozen source manifest: `logs/compact-parameter-square-sources.sha256`, SHA-256 `4cf819979cf47897d9421b5e577a883f03938f3350b47a260d003b36dfb5fb97`.
- Independent audit: `audits/CompactParameterSquareIndependentAudit.lean`.
- Evidence: `logs/compact-parameter-square-independent-20261009/`.
- Driver: `logs/compact-parameter-square-independent-driver.log`.
- Preparation/check scripts: `logs/prepare-compact-parameter-square-independent.py`, `logs/verify-compact-parameter-square-independent.sh`.
