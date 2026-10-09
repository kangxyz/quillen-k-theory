# Independent review: actual Reedy-arrow and quotient-row postcomposition

Status: accepted, 2026-10-09.

## Frozen sources

- `Quillen/Waldhausen/ExtensionCategory/Functoriality.lean`
- `Quillen/Waldhausen/SConstruction/Rows/Functoriality.lean`

The exact hashes are in
`logs/quotient-rows-functoriality-independent-20261009/sources.sha256`, copied
from the author's frozen manifest. Neither source was edited during review.

## Semantic review

Both sources were read completely, along with the relevant relative
cofibration, pointwise pushout, row, and reindexing APIs. Their hypothesis is
the genuine original `IsExact` witness for an ordinary functor between
Waldhausen structures. No conclusion about induced row exactness, homotopy,
or K-equivalence is supplied as an extra hypothesis.

Extension postcomposition is the original image-arrow functor, on both
objects and all commutative squares. The relative cofibration proof maps the
original displayed relative pushout using the input functor's pushout
preservation. The original comparison cofibration maps to a cofibration;
the choice-free relative criterion identifies the target's independently
chosen pushout by its actual universal property. No equality of chosen
pushout objects is asserted. Pushout preservation of extension arrows is
derived on the two original components and reflected by the full faithful
forgetful functor.

Quotient-row postcomposition retains the original interval diagrams and all
natural transformations. Original row zeros, cofibrations, and quotient
squares are mapped by the genuine exact functor. Every all-triples relative
cofibration test is preserved by the proved arrow result. Row pushouts are
then preserved using actual pointwise universal properties. The strict
source/middle/evaluation, horizontal-arrow, identity/composition, and every
ordinal-restriction identities concern these original functors.

Object and morphism universes are independent for source, target, and the
third category in composition. Zero preservation is genuinely `IsZero`;
there is no strict chosen-zero equality or endpoint-preserving ordinal-map
assumption. The boundary supplies structural functoriality only, without
claiming a fibration or a new K-theory equivalence.

## Independent checks

A fresh isolated artifact overlay excluded both live source-module artifacts.
The extension module and then the row module were freshly rebuilt. Lean's
`--deps` output verifies that the independent audit imports the fresh
artifacts. Both source logs and all consumers are warning-free.

`audits/QuotientRowsFunctorialityIndependentAudit.lean` recursively audits
exactly 27 declaration origins, including private/generated declarations:
13 extension-arrow origins and 14 quotient-row origins. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. Consumers retain independent
universes, original object/map components, actual target relative
cofibrations, genuine exactness, strict identity/composition and ordinal
restriction, all horizontal triples, actual zero preservation without a
chosen-zero equality, and pointwise weak-map preservation without assuming
reflection. The fixed27 guard executed successfully.

All source and inspected-dependency hashes match before/after. No live
compiled artifact was modified by this independent review.

Evidence: `logs/quotient-rows-functoriality-independent-20261009/`, including
`extension-check.log`, `rows-check.log`, `import-resolution.log`,
`origin-axioms-and-consumers.log`, and pre/post hash logs. The report, audit,
and evidence hashes are recorded by `deliverables.sha256` there.
