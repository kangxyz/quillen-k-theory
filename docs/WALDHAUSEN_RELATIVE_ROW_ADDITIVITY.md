# Genuine relative-row additivity and the original local fiber

## Checked endpoints

`Fibration.RelativeRows.Realization` constructs the genuine homotopy
equivalence `firstTailRealizationHomotopyEquiv N n`. Its forward map is
exactly the original `deloopingMap (firstTail_exact N n)` into the S-space of
the actual product category. Its inverse is the actual coproduct section,
using coproducts supplied by the genuine relative-row Waldhausen structure.

The actual product-S simplicial isomorphism then gives
`firstTailSSetRealizationHomotopyEquiv N n`, with forward map exactly
`(SSet.toTop.map (firstTailSSet N n)).hom`. This does not use or assert an
arbitrary ordinary-topological product homeomorphism.

`Fibration.RelativeRows.LocalFiber` identifies the row projection exactly
with the original tail map and retains the original realized fiber section
and literal constant chosen-zero path. `rowFiberInclusion_bijective` proves
bijectivity on every finite based homotopy set, including dimension zero.

## Proof content

The hard inverse composite is the original cutoff/identity/tail quotient
cofibration sequence. The cutoff arrow is genuinely exact in the Reedy
extension structure, including actual relative cube cofibrancy. The quotient
is the actual tail functor followed by its zero-first section, and its
cofiber squares are the original quotient squares. Actual functor additivity
identifies identity with tail-section plus cutoff. The genuine canonical
`first ⋙ fiber ≅ cutoff` identifies that sum with first/tail followed by the
original coproduct section.

For the reverse composite, the two original coproduct inclusions become
isomorphisms under first/tail evaluation, by exactness applied to the genuine
coproduct pushouts and actual zero objects. The resulting natural
isomorphism supplies the second inverse homotopy.

The local fiber conclusion applies the accepted split-product fiber
calculus to this proved equivalence and the strict original split triangle.
It assumes neither a homotopy-fiber comparison nor a commutative square
whose content is the conclusion.

## Scope

The categorical sum identification allows independent object/hom universes.
Realization and local homotopy-set endpoints explicitly use
`C : Type u` and `Category.{u} C`, matching the accepted original S-map API.
Only a genuine `NestedWeakEquivalences V` is required. No saturation,
extension, cylinder, kernel, cone, or closure assumption is added here.
The first-object evaluation and its splitting are degreewise; only the
accepted tail and fiber maps are claimed outer-natural.

The global connected-row diagonal homotopy-fiber theorem, quotient-choice
presentation, common-cylinder mixed comparison, and final original
change-of-weak-class fibration remain separate obligations.

## Evidence

Both source modules compile warning-free. Frozen source manifest:
`logs/relative-rows-realization-sources.sha256`.
Own audit: `audits/RelativeRowsRealizationAudit.lean`, checking every source
origin recursively and exact-map/universe/dimension-zero consumers.
Initial and terminal fixed24 audits both passed warning-free, covering
19 realization origins and5 local-fiber origins, with all17 exact consumers.
The terminal log is `logs/relative-rows-realization-audit-final.log`.
Source hashes rechecked against the frozen manifest; the evidence manifest
is `logs/relative-rows-realization-artifacts.sha256`.

Independent acceptance is recorded in
`docs/REVIEW_20261009_RELATIVE_ROW_ADDITIVITY.md`: both modules were rebuilt
in a fresh isolated overlay against independently checked cutoff/section
prerequisites, then fixed24 origins and all17 consumers passed with all
source/prerequisite hashes unchanged.
