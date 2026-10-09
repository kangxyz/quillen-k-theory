# The original joint-cylinder factorization on quotient rows

## Construction

`Fibration.Rows.JointFactorization` lifts structural base joint-cylinder data
to the exact same fine quotient-row category. The data are an actual exact
functor from pointwise arrows to genuine cofibration arrows, the two actual
endpoint coproduct injections with their colimit universal property, and
an actual coarse-weak projection satisfying the original factorization
identity. No row factorization, row exactness, or realization statement is
part of the input.

The accepted `QuotientRows.jointOnRows` retains every original component of
the joint arrow and proves its genuine all-triples Reedy row cofibrancy.
The two endpoint injections give an actual row pushout over the chosen zero:
this follows from each displayed coproduct pushout and the proved pointwise
pushout theorem. Cobase change makes the first endpoint injection a genuine
row cofibration. Composing it with the joint arrow gives the actual original
first factor. The projection and factorization equation are checked at each
unchanged interval.

Middle exactness for fine weak maps follows from genuine exact joint-row
postcomposition and the exact target evaluation of the cofibration-arrow
category. Fine-square preservation is then a consequence of that exactness.
The first and last factors and the middle functor retain their original
component formulas. Every ordinal restriction commutes with the middle
functor and both factors literally. Coarse middle exactness also follows
from the actual projection and coarse two-out-of-three when that base
condition is available; fine exactness uses no saturation.

## Concrete complexes

`Fibration.Rows.ComplexFactorization` supplies all the base structural data
from the accepted actual identity-cone joint cylinder. Its first factor at
an interval is the original identity-cone inclusion, and its projection is
the original quasi-isomorphism projection. The row factorization has the
original fine Reedy cofibration class and the pointwise coarse
quasi-isomorphism class on the same row objects.

The hypotheses are an abelian base category with independent object and hom
universes, and a full complex subcategory containing zero and closed under
isomorphisms, extensions, finite products, actual mapping cones, and shift
by one. Shift closure is retained from the genuine joint-cylinder exactness
theorem. No kernel closure or projectivity assumption enters.

## Scope and verification

This supplies structural row-level input to the original finite-chain
replacement. It does not infer a fine equivalence from the coarse projection,
and does not claim the global diagonal homotopy-fiber theorem.

Both implementation sources passed warning-free focused checks. The initial
single-traversal recursive audit passed all 72 declaration origins (57 generic
and 15 concrete), allowing only `propext`, `Classical.choice`, and `Quot.sound`.
All 27 consumers passed, including original maps, genuine Reedy cofibrations,
actual endpoint coproducts, strict reindexing, independent universes, degree
zero, bounded terms without kernel closure, and arbitrary schemes.

- Frozen source manifest: `logs/row-cylinder-factorization-sources.sha256`
- Audit: `audits/RowCylinderFactorizationAudit.lean`
- Source logs: `logs/row-joint-factorization-check.log` and
  `logs/row-complex-factorization-check.log` (both empty)
- Terminal audit: `logs/row-cylinder-factorization-audit-final.log`

The fixed72 terminal audit passed with all27 consumers warning-free, and
before/after source hashes match. Independent review is separate and pending.
Full evidence: `logs/row-cylinder-factorization-artifacts.sha256`.
