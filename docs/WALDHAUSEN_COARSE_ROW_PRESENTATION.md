# Actual coarse row presentation

Source: `Quillen/Waldhausen/Fibration/MixedNerves/CoarseRows.lean`.

For the genuine nested pair `N`, the original fine and coarse quotient-row
object predicates are proved equivalent by `isRow_coarse_iff`. The only
structure-dependent condition is the original cofibration predicate,
transported by `N.cof_eq`; zero objects and displayed pushout squares
are absolute categorical conditions.

`coarseRowView` and `fineRowView` retain each original diagram and natural
transformation. Their composites are proved literally identity functors.
Restricting to the original componentwise coarse weak maps gives the
actual `coarseWeakRowsEquivalence` between:

- `coarseWeakRows N m`: coarse weak maps on the unchanged fine row objects;
- `QuotientRows.WeakRows N.coarse m`: the standard coarse weak row model.

Both functors retain the original component diagrams and maps, and both
commute strictly with original ordinal restriction. The source restriction
`coarseWeakRowsReindex` is the literal `widePostcompose` supplied by
`rowReindexCompatible`, matching the coarse-chain augmentation's target.

`coarseWeakRowNerveIso` is a genuine bisimplicial isomorphism to the standard
coarse weak-row nerve. `coarseSSetIso` composes its diagonal with the checked
original-grid presentation to identify the source with the actual coarse
Waldhausen simplicial set. The forward map is the original weak-chain grid
reconstruction. Exact whole-functor and every-object formulas are exposed;
the audit also checks its maps and the inverse grid components.

All statements retain independent object and hom universes `u,v`, with
nerves in `SSet.{max u v}`. There is no extension, saturation, cylinder,
row-exactness, or homotopy-fiber assumption. This is an actual categorical
and simplicial presentation change, not a new global fibration theorem.

The source uses the separately frozen `Rows/NervePresentation` boundary.
Its independent review is tracked by the parent alongside this adapter.
The focused source build and all 40 recursive declaration origins with
23 consumers pass warning-free, including the terminal fixed40 replay.
The fixed40 guard is in
`audits/MixedNervesCoarseRowsAudit.lean`. Source manifest:
`logs/mixed-nerves-coarse-rows-sources.sha256`, fingerprint
`aa8322ff778c438afffc07dc9eaa46b06cffee782df8f72de66053335f5a6cb6`.
Evidence manifest: `logs/mixed-nerves-coarse-rows-artifacts.sha256`.
