# The original total inner-row mixed inclusion

`MixedNerves/TotalRealization` imports the frozen postcomposition layer and
accepted genuine row mixed-inclusion equivalences. The original quotient-row
restriction makes `rowDiagonalInclusion N` a genuine bisimplicial map.
For each inner row degree its component is definitionally the original
mixed inclusion on the same genuine quotient-row category.

`totalChainInclusionRealizationHomotopyEquiv N D hs` applies the proved
generic bisimplicial realization-invariance theorem to those actual row
equivalences. Its forward map is definitionally
`SSet.toTop.map (TheoremA.diagonalMap (rowDiagonalInclusion N))`.
Thus all three original indices are totalized with the actual inclusion
forward. No compatibility of chosen homotopy inverses is required.

The genuine base inputs are the original joint-cylinder data, its actual
second-endpoint section, and coarse two-out-of-three. They are discharged
for complex subcategories by `complexTotalChainInclusionRealizationHomotopyEquiv`
using the actual mapping cylinder and proved quasi-isomorphism saturation.
The stated mapping-cone/shift closure remains explicit. Bounded-term
consumers derive those conditions from the accepted bounded-terms model,
without kernel closure.

The realization scope is a common object/hom universe. The preceding
postcomposition and diagram layers retain independent `u,v`.
The original relative-inner-S/GridBridge and weak-filtration presentation
identifications are separate; the global relative-realization fiber theorem
is still a separate obligation. This endpoint alone is not a global
fibration or Gillet-Waldhausen theorem.

Verification is recorded by the combined four-source manifest
`logs/mixed-nerves-postcomposition-total-sources.sha256` and
`audits/MixedNervesTotalAudit.lean`. The latter checks every origin
recursively and 37 original-map consumers, including the literal final
forward map, original third-index component, all-zero simplex, independent
structural universes, and genuine bounded-term specialization.

All four focused source builds and the terminal fixed118 audit
(57+22+29+10) with all 37 consumers passed warning-free, including two
literal third-index object/map consumers. Source and evidence manifests:
`logs/mixed-nerves-postcomposition-total-sources.sha256` and
`logs/mixed-nerves-postcomposition-total-artifacts.sha256`.
