# Independent review: actual complex-cylinder pushouts

Status: accepted, 2026-10-09.

## Frozen boundary

The exact two sources are recorded in
`logs/cylinder-pushout-independent-20261009/sources.sha256`:

- `Quillen/CategoryTheory/Limits/BiproductPushout.lean`
- `Quillen/Waldhausen/Cylinder/Pushout.lean`

Both sources were read completely. Neither was changed during review.

## Semantic contract

`isPushout_biprod_map` constructs the genuine universal property of the
literal biproduct square of two displayed pushout squares. It assumes only a
preadditive category with binary biproducts. It does not require abelianness,
chosen pushouts, monomorphisms, or split maps.

`isPushout_of_degreewise` derives commutativity and the actual complex
pushout universal property from the corresponding degreewise properties,
using evaluation's joint detection of colimits. `identityConeTermIso` is the
actual mapping-cone term decomposition into the original neighboring terms;
both its forward projections and inverse inclusions are checked. Its
naturality concerns the original mapping-cone map. Transporting the literal
biproduct pushout squares through these genuine term isomorphisms proves
that the original identity-cone functor preserves every displayed pushout.

Finally `middleFunctor_map_isPushout` concerns the original cylinder middle
functor and its original biproduct map. It requires precisely componentwise
pushout squares on the source and target components of the arrow square.
It has no hidden cofibration or weak-equivalence hypothesis. The theorem
provides a structural pushout-preservation input; it does not assert a
fibration theorem or an equivalence of K-theory models.

## Independent verification

A fresh artifact overlay excluded both source modules' live artifacts.
Both sources were rebuilt directly, in order, under compiler slot2. The
independent audit imported the freshly rebuilt cylinder artifact, as recorded
by Lean's `--deps` output. All build and audit checks are warning-free.

`audits/CylinderPushoutIndependentAudit.lean` recursively checks exactly all
16 source-origin declarations, including private/generated declarations,
against the allowed axioms `propext`, `Classical.choice`, and `Quot.sound`.
The independent consumers use arbitrary object/hom universes, the minimal
preadditive hypothesis for the generic square, unchanged original cone
forward/inverse maps and naturality, and the original literal middle map.
No statement-shaped universal-property conclusion is supplied as an extra
hypothesis beyond the displayed input squares.

Source and inspected dependency hashes were checked before/after; all match.
No live compiled artifact was modified by this independent review.

Evidence: `logs/cylinder-pushout-independent-20261009/`, including
`biproduct-check.log`, `cylinder-check.log`, `import-resolution.log`,
`origin-axioms-and-consumers.log`, and the pre/post hash logs. The audit,
report, and evidence files are recorded by `deliverables.sha256` there.
