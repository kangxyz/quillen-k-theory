# Independent review: the original bar augmentation fiber maps

## Scope and semantic result

The two unchanged sources in
`logs/two-sided-bar-fiber-independent-20261009/sources.sha256` were read
completely. Their exact augmentation/naturality dependencies were inspected
against the independently accepted seven-source bar boundary; the generic
weak-square transport is now independently accepted as well. No semantic
issue was found. **Accepted for this scope.**

For an arbitrary actual transformation `η : H ⟶ J` of simplicial diagrams,
`barMap`, `replacementMap`, `dropMap`, and evaluation use the original
simplicial maps. Both realized squares commute strictly in the orientation
required by the existing homotopy-fiber API. The induced `dropFiberMap` and
`evaluationFiberMap` have exactly the original realized augmentation on
the source coordinate and postcompose the whole original path with the
corresponding base augmentation. These four formulas are literal `rfl`
identities; no path is silently contracted or replaced.

The accepted genuine drop and evaluation homotopy equivalences have these
exact forward maps. Applying the proved weak strict-square transport gives
the empty-aware weak property for both original fiber maps, with no
condition on `η` and no assumed fiber equivalence. Every finite original
homotopy-set map is bijective at every supplied point, including degree
zero. Component surjectivity and empty-fiber behavior are explicit. The
original degree-zero simplicial vertex and its realized evaluation point
are retained. No based inverse or Whitehead upgrade is used.

The diagrams have arbitrary coefficient universe `u` and the actual
universe-aligned indexing construction from the accepted bar boundary.
This is the genuine augmentation fiber zigzag. The replacement-fiber
comparison, finite weak-cartesian gluing, and final Waldhausen canonical
fiber-map identification remain separate obligations.

## Independent verification

An isolated first-`LEAN_PATH` overlay excludes both reviewed artifacts and
uses the fresh independently checked weak-fiber and weak-square artifacts
as prerequisites. The exact accepted bar7 and weak-square2 source manifests
are rechecked around the run. The count-frozen audit checks all **18**
defining origins, including any private/generated declarations and their
recursive axioms, permitting only `propext`, `Classical.choice`, `Quot.sound`.

There are **22** exact consumers: original source/path coordinates, strict
realized squares, exact genuine augmentation-equivalence forward maps,
all finite degrees, explicit π0, original simplicial and realized vertices,
component surjectivity for both sides, constant-path points for both sides,
and empty-source-fiber consequences for both targets.

Audit: `audits/TwoSidedBarFiberIndependentAudit.lean`.
Script: `logs/verify-two-sided-bar-fiber-independent.sh`.
Evidence: `logs/two-sided-bar-fiber-independent-20261009/`.
Both fresh source builds, the fixed18 recursive audit, and all22 consumers
passed warning-free. Source and accepted prerequisite hashes match after
the run. Per-module origin counts are 14 and 4. The manifest fingerprint is
`1a25859ad18fb0c481985aede7a97a225c6fc39c2fa2c9618e39ea5b966d5cad`.
Final logs: `check.log`, `audit-final.log`, `deps.log`, and the before/after
hash records in the evidence directory. All checks use shared slot1 and
`-j1`; no production source is modified and no live Lake rebuild is run.
