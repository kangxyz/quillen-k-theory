# Genuine quotient-row/arrow interchange and exact joint-functor lift

## Frozen boundary

The eight new sources are listed in `logs/row-arrow-interchange-sources.sha256`:

1. `Quillen/CategoryTheory/ArrowDiagrams.lean`
2. `Quillen/Waldhausen/ExtensionCategory/PostcomposeDetection.lean`
3. `Quillen/Waldhausen/SConstruction/Rows/PointwiseArrows.lean`
4. `Quillen/Waldhausen/ExtensionCategory/TriplePushout.lean`
5. `Quillen/Waldhausen/ExtensionCategory/Transpose.lean`
6. `Quillen/Waldhausen/ExtensionCategory/TransposeExact.lean`
7. `Quillen/Waldhausen/SConstruction/Rows/ReedyArrows.lean`
8. `Quillen/Waldhausen/SConstruction/Rows/JointFunctor.lean`

Every source has a warning-free direct Lean check. Earlier accepted source
boundaries are unchanged. These are categorical statements with independent
object/hom universes. They assert no cross-universe realization comparison.

## Exact endpoints

For any genuine `W : Waldhausen.Structure C` and original ordinal `n`:

- `QuotientRows.pointwiseArrowEquivalence W n` identifies the entire arrow
  category of actual quotient rows with actual quotient rows valued in the
  pointwise arrow Waldhausen category.
- Its original functor and inverse, `arrowToRows` and `rowsToArrow`, are
  genuinely exact (`arrowToRows_exact`, `rowsToArrow_exact`).
- `QuotientRows.reedyArrowEquivalence W n` identifies genuine Reedy
  cofibration arrows between quotient rows with quotient rows valued in the
  genuine Reedy cofibration-arrow category.
- Its original functor and inverse, `reedyToRows` and `rowsToReedy`, are
  genuinely exact (`reedyToRows_exact`, `rowsToReedy_exact`).

Both equivalences preserve the literal original component diagrams and
component maps. The two composites are strictly the identity functors.
All four functors commute strictly with every ordinal restriction.

Given an actual exact functor `J : Arrow C ⥤ ExtensionCategory.Obj W` from
the pointwise arrow structure associated to `V` to the Reedy extension
structure associated to `W`, `jointOnRows V W hJ n` is literally

`arrowToRows V n ⋙ postcompose hJ ⋙ rowsToReedy W n`.

`jointOnRows_exact` proves genuine exactness of this actual composite.
`jointOnRows_obj_hom_app` retains the original joint map at every quotient
component. The two morphism-component formulas retain the original `J.map`
squares, and `jointOnRows_reindex` is strict equality for every ordinal map.
Source and target categories of `J` can have independent universes.

## The nontrivial relative-pushout proof

Categorical equivalence alone does not prove preservation of a Waldhausen
cofibration class. The proof explicitly supplies the missing structure:

- `mapped_relative_cof` tests the original relative comparison using its
  actual image pushout. `cof_of_postcompose_family` then lifts concrete
  joint detection of ambient cofibrations to joint detection of Reedy
  cofibrations. Row applications supply the original all-triples predicate
  itself as the detection proof.
- A cofibration square can be transposed by flipping its actual relative
  pushout and retaining the original relative comparison map. This gives
  `transposeSquare` and the literal categorical involution `transpose`.
- A morphism between such squares is a three-direction cube. Its two
  iterated relative pushouts are not silently identified. The theorem
  `relativePushoutInterchange` constructs the comparison map and proves
  the newly displayed pushout by an explicit universal-property descent
  and uniqueness argument. Only the actual displayed pushouts and their
  boundary equations are inputs; no global colimits or new pushout
  conclusion is assumed.
- `transpose_cof` applies that actual interchange to the two original
  relative pushouts of the cube, retaining the original total comparison
  cofibration. `transpose_exact` separately proves zero/weak/pushout
  preservation. Only pushout preservation uses the already genuine
  categorical equivalence.
- These cube tests prove both directions of the Reedy row interchange.
  Quotient conditions use actual component pushouts. No row exactness or
  transposed-cofibration conclusion is supplied as an assumption.

## Verification

`audits/RowArrowInterchangeAudit.lean` recursively checks every declaration
origin in the eight modules against only `propext`, `Classical.choice`, and
`Quot.sound`. Its exact consumers test independent category universes,
original component maps, both actual equivalences and all four exact
functors, the real cube cofibration result, ordinal reindexing, and the
actual lifted joint functor. Concrete consumers use the accepted complex
joint-cylinder functor for both the isomorphism and quasi-isomorphism
weak models, rather than assuming a row-level exactness witness.

The fixed audit covers **139 declaration origins** (26, 3, 19, 2, 26, 2,
51, and 10 in manifest order) and **33 exact consumers**, including both
actual complex-cylinder weak models. The audit log is
`logs/row-arrow-interchange-audit.log`; source and evidence hashes are
recorded in the corresponding source/artifact manifests. The source-manifest
SHA-256 is `152b52da6b175107bb041727965126af12674444fc52f0fb4c2cf46008d8d2fb`. No `sorry` or new axiom occurs in this boundary.

## Remaining fibration scope

The actual relative-row subcategories, relative additivity retaining its
split fiber inclusion and exact tail projection, and common-cylinder mixed
comparison remain separate steps. The generic connected-row diagonal
homotopy-fiber theorem is an independent topological obligation. Neither
these equivalences nor a rowwise realization comparison alone supplies it.
