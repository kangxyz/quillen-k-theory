# Literal mixed-nerve postcomposition and inner-row naturality

Frozen three-source boundary:
`MixedNerves/Postcompose`, `PostcomposeNerves`, and `RowPostcompose`.
All three focused source builds pass warning-free. Source manifest:
`logs/mixed-nerves-postcomposition-sources.sha256`, fingerprint
`48f200fb1c83929f781e9d0ce320b494b447277ed03dd5ccbf659fac333b55d9`.

## Actual forward diagrams

`CompatibleFunctor N M` contains an actual functor and preservation of the
original fine-weak, fine-cofibration, and coarse-weak arrow predicates.
These are structural arrow statements; no exactness, nerve equivalence,
realization conclusion, or target square is assumed. Identity and actual
composition are supplied.

`finePostcompose`, `coarsePostcompose`, and `cofPostcompose` apply that
original functor to the existing chains. Their weak-category restrictions
retain its original component maps. All four nerve maps commute strictly
with original ordinal restrictions. Their identity/composition laws and
strict squares with the original inclusions are proved. Both transpose
isomorphisms, including their diagonal forms, commute strictly with the
same base functor.

`rowReindexCompatible N α` instantiates the structural data using the
original quotient-row restriction. All three preservation statements
come from the accepted genuine fine/coarse reindex exactness; no row
exactness input is added. Its original functor, identity and composition
are identified explicitly.

`coarseRowNerves`, `cofRowNerves`, `horizontalRowNerves`, and
`horizontalCofRowNerves` are actual diagrams in the inner row degree.
The original inclusions are strictly natural in this third index.
`coarseRowDiagonals`, `cofRowDiagonals`, and `rowDiagonalInclusion`
provide the resulting bisimplicial diagrams for total realization.
Every component of `rowDiagonalInclusion` is definitionally the original
mixed diagonal inclusion on that genuine quotient-row category.

## Scope

All sources allow independent object and hom universes `u,v`.
Base source and target categories share those universe levels, as
required by the current nerve-map API; the nerves live in
`SSet.{max u v}`. There is no coarse saturation, extension axiom, cylinder,
or homotopy-equivalence assumption. No naturality of chosen homotopy
inverses is inferred. The common-universe realization endpoint and the
original relative-inner-S/GridBridge identification remain separate.

## Verification

`audits/MixedNervesPostcomposeAudit.lean` checks every declaration origin
recursively against the three standard axioms and includes 30 consumers:
original object/component maps, both original inclusion and transpose
squares, genuine row cofibration/coarse preservation, all four composition
laws, original third-index maps, independent universes, and degree zero.
All 108 origins (57+22+29) and all 30 consumers passed warning-free.
The final combined audit also includes the separate totalization endpoint.
