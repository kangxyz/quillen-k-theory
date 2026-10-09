# Original weak source change and weak-cartesian pasting

The two sources `Quillen/Topology/HomotopyPullback/WeakSource.lean` and
`WeakPasting.lean` retain the existing compact-open-path homotopy pullbacks and
canonical constant-path comparisons.

## Source change

`sourceProjection_homotopyLiftingProperty` proves the actual source projection
is a genuine fibration, using the existing path-reversal homeomorphism and
actual base-projection fibration.

`sourceMapPullbackHomeomorph` identifies source change with the strict pullback
of the source map along that projection. Its inverse keeps the entire original
path. The already proved weak right-proper theorem therefore yields
`sourceMap_isWeakHomotopyEquivalence`: a complete weak source equivalence
induces a complete weak equivalence on the original total homotopy pullbacks.

## Pasting

`pastingComparison_factorization` identifies the original outer canonical
comparison, followed by the genuine nested-pullback homotopy equivalence,
with the original source-change map followed by the first comparison. The
identity is proved on both source coordinates and both complete paths.
`comparison_paste_isWeakHomotopyEquivalence` follows by weak source change,
composition, and empty-aware two-of-three.

All spaces lie in one arbitrary common universe. No nonemptiness,
connectedness, separation or local compactness hypothesis is added. Component
surjectivity and every finite based degree, including zero, are part of the
conclusion.

## Validation boundary

The frozen source manifest is `logs/weak-pullback-pasting-sources.sha256`.
Both sources compiled warning-free. The recursive origin scan found exactly
fifteen declarations (including generated homeomorphism proofs), using only
`propext`, `Classical.choice` and `Quot.sound`.
`audits/WeakPullbackPastingAudit.lean` fixes this count and tests thirteen actual
map/path, degree-zero and empty-source consumers. Its final run is recorded in
`logs/weak-pullback-pasting-fixed15.log`.

This supplies source-change and pasting closure. It does not establish the
remaining finite weak-cartesian pushout/gluing theorem.
