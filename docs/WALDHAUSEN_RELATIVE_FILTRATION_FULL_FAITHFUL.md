# Full faithfulness of the original relative initial filtration

## Mathematical result

`initialFiltrationFunctor N n` retains the actual initial chain and every
original component map. `FiltrationFullFaithful` constructs its actual
inverse on morphisms, proves that it is full and faithful, and exports
`initialFiltrationFullyFaithful` with that original inverse definitionally.

The construction is generic in independent object/hom universes. It needs
only a genuine nested Waldhausen structure and the already-defined actual
relative quotient rows. There is no extension, saturation, cylinder,
preadditive, exact-category, or equivalence hypothesis.

## Original maps

An arbitrary transformation between the two initial chains is augmented at
the omitted initial vertex by the unique map from the actual source zero
object. Each interval component is then descended through the original
source quotient pushout. The descent compatibility uses the actual target
quotient square and factorization through its genuine zero corner.

`originalQuotient_extendFiltrationAt` records the exact original quotient-map
formula. `extendFiltrationAt_initial` identifies every unchanged original
initial component. Naturality and uniqueness are proved by the original
quotient pushout universal properties, including degenerate intervals.
The exported fully-faithful datum has preimage exactly `extendFiltrationMap`,
rather than an unspecified choice of a map with the desired image.

Fine weakness of a pointwise fine-weak original chain transformation is
preserved by this extension, through the separately proved actual quotient
weak-map detection. No fine saturation is needed.

## Scope boundary

This is full faithfulness into the raw category
`ComposableArrows C n.len`. It does not claim essential surjectivity onto
all raw chains. A completion for the actual cofibration/coarse-weak essential
image and the resulting quotient-presentation equivalence are separate.
No realization, mixed-grid, or homotopy-fiber conclusion occurs here.

## Verification

The source compiled warning-free. Initial and terminal fixed49 recursive
origin audits passed, restricted to `propext`, `Classical.choice`, and
`Quot.sound`. All12 independent-universe and original-map consumers passed,
including the exact preimage, original quotient formula, actual zero
augmentation, uniqueness and fine-weak extension.

Frozen source manifest:
`logs/relative-rows-filtration-full-faithful-sources.sha256`.
Own audit: `audits/RelativeRowsFiltrationFullFaithfulAudit.lean`.
Terminal log: `logs/relative-rows-filtration-full-faithful-audit-final.log`.
Evidence: `logs/relative-rows-filtration-full-faithful-artifacts.sha256`.
Source hashes were rechecked after the terminal audit. Independent review is
separate.
