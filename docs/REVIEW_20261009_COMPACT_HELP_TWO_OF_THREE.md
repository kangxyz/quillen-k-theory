# Independent review: compact HELP cancellation and split transitions

Accepted 2026-10-09 09:11 UTC. All eight sources in
`logs/compact-help-two-of-three-20261009/sources.sha256` were read completely,
freshly rebuilt in an isolated overlay, and recursively audited with a fixed
43-origin guard. All 30 exact-map consumers passed. Source builds and audits
are warning-free, hashes match, and only propext, Classical.choice, and
Quot.sound occur recursively.

The strict-square/full-boundary equivalence is genuine: it extends the
prescribed reversed boundary homotopy, then removes its actual constant
padding. First cancellation lifts compact boundary data through the first
map, extends the correction by HEP, and contracts the resulting retracing
homotopy relative to both endpoints. Second cancellation uses the actual
compact pushout cylinder boundary; HEP is proved from the interval-square
extension theorem. Neither embedding nor Hausdorff assumptions are hidden.
Homotopy invariance likewise corrects the whole boundary retracing.

Actual strict sections and strict or homotopy-commuting transitions inherit
compact HELP by the proved cancellation statements. The realization
application keeps the literal constant-path split inclusion and original
first projection. Its input is the actual original first/tail realization
homotopy equivalence, with its exact forward-map identification; it does not
assume the resulting fiber comparison or a continuous inverse family.

Two added consumers invoke the resulting full HELP statements with arbitrary
prescribed boundary homotopies, after first cancellation and after the section
construction. Existing consumers include actual cylinder pushout/HEP,
retracing, both cancellation directions, homotopy invariance and exact split
realization transitions. Global weak-cartesian gluing remains separate.

Evidence: `logs/compact-help-independent-{prehash,build,audit,posthash}.log`;
`audits/CompactHELPTwoOfThreeIndependentAudit.lean`;
replay `logs/verify-compact-help-independent.sh`.
