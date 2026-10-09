# Independent review: exactness of the actual joint-cylinder functor

Date: 2026-10-09. Result: **accepted for the frozen three-source structural boundary**.
No implementation source was changed.

## Exact contract

Let `A : Type u` carry `Category.{v} A` and an abelian structure, with independent
object and hom universes. Let `P` be an actual object property on cochain complexes
in `A`. The endpoint assumes:

- `P.ContainsZero` and closure under actual isomorphisms;
- extension closure for the ambient abelian exact structure;
- `P.IsClosedUnderFiniteProducts`;
- closure under the actual mapping cone of every map between `P`-objects;
- closure under the actual shift by `1`.

The domain is the **entire** arrow category of `P.FullSubcategory`, with genuine
pointwise inherited admissible cofibrations. The target is the actual category
of cofibration arrows with the previously independently accepted source-plus-
relative-target Reedy cofibration class.

`subcategoryJointFunctor P hcone hshift` sends the original arrow to the original
joint endpoint inclusion. Its left component is the literal ambient biproduct
map and its right component is the original cylinder middle functor. The
composition with target source evaluation is definitionally
`subcategoryJointSourceFunctor P`; composition with middle evaluation is
definitionally `subcategoryMiddleFunctor P hcone`. Both unchanged component
formulas are tested independently.

`subcategoryJointFunctor_quasiExact` proves genuine structural exactness for
actual quasi-isomorphism weak equivalences.
`subcategoryJointFunctor_isoExact` proves exactness of the **same functor** for
actual isomorphism weak equivalences. The object and cofibration classes are
definitionally the same in these two models; only the weak class changes.

## Proof checks

I read all three complete sources, the ordinary-admissibility argument in
`AmbientRelative.lean`, and the relevant original quotient/pushout interfaces.

1. The middle cylinder preserves genuinely zero arrows: the original projection
   becomes an actual isomorphism to the target when the source is zero, and the
   target is zero. Reflection in the full subcategory proves its own zero property.
2. The middle map is a quasi-isomorphism if the **target** component is one. The
   proof applies the established actual identity-cone cylinder theorem; no weak
   hypothesis on the source component is needed for this supporting result.
3. Actual displayed component pushouts along inherited admissible maps become
   ambient pushouts using the proved full-subcategory inclusion theorem. The
   original middle functor preserves those displayed ambient squares, and full
   faithfulness reflects their actual universal properties.
4. Every object joint inclusion is an actual inherited cofibration. For a map
   of joint cylinders, a genuine relative pushout and its actual comparison map
   are constructed. The ordinary admissibility theorem identifies the relative
   quotient with the **shifted actual cokernel of the original source map**.
   Its membership comes from inherited admissibility and the supplied shift
   closure. No degreewise splitting or arbitrary quotient closure is assumed.
5. The intermediate Reedy lemma explicitly separates source-sum admissibility.
   The final exactness theorem discharges it using the actual joint-source
   exact functor, rather than retaining it as an input.
6. Arbitrary displayed arrow pushouts along pointwise cofibrations are genuinely
   pointwise by the independently accepted arrow-category theorem. Exactness of
   the source and middle components then proves the actual displayed pushout in
   the cofibration-arrow category. No preservation conclusion is a hypothesis.
7. For the isomorphism model, pointwise isomorphisms make the actual arrow map
   invertible, so the original functor preserves them. No quasi-isomorphism-to-
   isomorphism implication is used.

The actual joint-source helper was authored separately by this reviewer and
independently rebuilt/audited/accepted by the parent in
`docs/REVIEW_20261009_CYLINDER_JOINT_SOURCE.md`. This review covers only the other
three sources; it is not self-review of that helper.

## Independent verification

The three frozen sources were rebuilt in order into an isolated overlay.
Fresh artifacts from the preceding independent row/arrow and extension-embedding
reviews supply those dependencies; other unchanged dependencies are linked.
No production olean was replaced. Checks used Lean 4.34.0, `-j1`, and slot1, with
acquisition recorded. All source checks were warning-free.

`audits/JointCylinderIndependentAudit.lean` has a fixed **21-origin** guard.
It enumerates exact defining-module origins, including private/generated
constants, and recursively allows only `propext`, `Classical.choice`, and
`Quot.sound`. All 21 origins and all **12 independent consumers** passed without
warnings. Consumers preserve independent object/hom universes, both exact weak
models, the original object and morphism formulas, source/middle composition
equalities, target-only middle quasi-isomorphism preservation, arbitrary zero
preservation, Reedy cofibrations without a supplied source-sum condition, and
actual displayed pushout preservation. All source hashes match before building,
after building, and after the audit.

## Limits

This establishes the genuine common joint-cylinder exactness input for the iso
and quasi-isomorphism models under the stated ordinary property closures.
It is not a Waldhausen fibration theorem, relative-realization equivalence,
Gillet–Waldhausen comparison, or scheme/perfect K-equivalence. Strict chosen-zero
normalization and the remaining topological fiber comparison are separate
obligations wherever their later interfaces require them.

## Frozen sources and evidence

- `Quillen/Waldhausen/Cylinder/SubcategoryPreservation.lean`:
  `559a23e398ec474aa235471807cc7f70c0a3c14b3d219100a02a70f188be7131`
- `Quillen/Waldhausen/Cylinder/JointFunctor.lean`:
  `f7bc75f93b49268224e8e2d50819c0fab2f89992f1f33d5064e59d4d3db2a742`
- `Quillen/Waldhausen/Cylinder/JointExact.lean`:
  `0b43a7722176ad6949167e0332b8754f5f8f7664339c33a318a1c2c7f01e9d37`

Manifest: `logs/cylinder-joint-exact-independent-20261009/sources.sha256`.
Manifest SHA-256:
`853abeac1947e84e11a273cce9f7d31fafca1a968d07df6256b24ed30853772f`.

That directory contains `check.log`, `deps.log`, `audit.log`, the three
`hashes-*.log` rechecks, and `artifacts.sha256` with exact report/audit/script/log
and fresh-artifact hashes. The ordered build/acquisition record is
`logs/cylinder-joint-exact-independent-session.log`.
