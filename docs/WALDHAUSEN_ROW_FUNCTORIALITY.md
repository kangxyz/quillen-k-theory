# Exact postcomposition of Reedy extension arrows and quotient rows

## Contract

The new modules are:

- `Quillen/Waldhausen/ExtensionCategory/Functoriality.lean`
- `Quillen/Waldhausen/SConstruction/Rows/Functoriality.lean`

They depend on the separately frozen quotient-row/pointwise-arrow boundary
and do not edit it. All results allow independent source and target object
and hom universes: `C : Type u`, `Category.{v} C`, `D : Type u'`,
`Category.{v'} D`.

Given genuine Waldhausen structures `V`, `W` and a functor `F : C ⥤ D`
with its actual `IsExact V.cof V.weq W.cof W.weq F` witness:

- `ExtensionCategory.postcompose V W hF` is the original image-arrow
  functor on all actual cofibration arrows and all their commutative squares.
- `ExtensionCategory.postcompose_exact` proves genuine exactness for the
  source-plus-relative-target cofibration structures.
- `QuotientRows.postcompose V W hF n` is literal postcomposition on the
  original quotient diagrams and their natural transformations.
- `QuotientRows.postcompose_exact` proves genuine exactness for the
  all-triples Reedy row structures.

Both layers have exact object/map component formulas and strict identity
and composition equalities. Extension postcomposition commutes strictly
with source and middle evaluation. Row postcomposition commutes strictly
with every quotient evaluation, every horizontal-arrow functor, and every
ordinal restriction.

## Proof of the relative condition

For a Reedy square, map its actual original relative pushout through `F`.
`hF.pushout` gives the genuine displayed relative pushout in the target.
The original comparison map is a cofibration, so its actual image is a
cofibration by `hF.cofibration`. The already proved choice-free
`ExtensionCategory.cof_of_relative` supplies the target's actual Reedy
condition. It uses the unique isomorphism between displayed and chosen
pushouts internally; no equality of independently chosen pushout objects
is assumed.

All-triples row cofibrations follow by applying this result to every
horizontal interval arrow. Row pushout preservation follows from the
proved pointwise pushout theorem and the original exact functor's actual
pushout preservation. Zero preservation is the genuine `IsZero` condition;
there is no unproved strict equality between `F.obj V.zero` and `W.zero`.

## Verification boundary

Both source modules passed warning-free direct Lean checks. The frozen
manifest is `logs/quotient-rows-functoriality-sources.sha256`. The fixed
recursive audit covers **27 declaration origins** (13 extension and 14 row)
and **17 exact-map consumers**, allowing only `propext`, `Classical.choice`,
and `Quot.sound`. The audit is
`audits/QuotientRowsFunctorialityAudit.lean`; its log is
`logs/quotient-rows-functoriality-audit.log`. No new axioms,
`sorry`, assumed row exactness, realization equivalence, or homotopy-fiber
conclusion is introduced.
