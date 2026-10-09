# Independent review: inherited joint and relative cylinder cofibrations

Accepted 2026-10-09 05:53 UTC after full semantic inspection, fresh isolated
rebuild of both frozen sources, fixed-count recursive axiom audit,
arbitrary-universe/minimal-input consumers, and pre/post source rehashes.

## Accepted scope

`Quillen/CategoryTheory/ExactCategory/SubcategoryCokernel.lean` proves that
an actual ambient cokernel of an inherited admissible monomorphism belongs
to the inherited object predicate. It first extracts the actual conflation
and its quotient object in the predicate. Uniqueness of genuine cokernels
then supplies the isomorphism to the specified ambient cokernel, and
repleteness transports membership. The ambient category need not be abelian;
only the particular cokernel must exist. This is not arbitrary cokernel or
quotient closure.

`Quillen/Waldhausen/Cylinder/Subcategory.lean` retains the original two
endpoints, original factorization middle object, actual joint map, and
actual relative map. Cone closure supplies the middle object through the
accepted factorization machinery. The actual joint quotient is the shifted
source object. The relative quotient is exactly the shifted actual cokernel
of the map on sources. Inherited admissibility puts that actual cokernel in
the predicate, and shift closure supplies the relative quotient membership.
The inherited conflations and degreewise split monomorphism conclusions
then give the displayed split cofibrations.

Only the source component of the arrow square is required to be a split
cofibration. No cofibration hypothesis on its target component, global
projectivity, arbitrary quotient closure, approximation theorem, or
K-equivalence conclusion is inserted. The statement's ambient pushout
hypothesis is usable from an ordinary inherited pushout: the independent
consumer derives the ambient universal property using the proved inherited
joint cofibration and the accepted full-subcategory pushout theorem.

## Independent verification

The two sources were rebuilt into an isolated artifact overlay in dependency
order. Neither live source-origin olean was reused or replaced. Both fresh
build logs are empty. `--deps` confirms that the second source and audit
resolve the freshly rebuilt artifacts. Previously accepted dependencies were
reused and their inspected source hashes were checked afterward.

`audits/CylinderSubcategoryIndependentAudit.lean` checks exactly 11
source-origin declarations, including private/generated declarations, and
recursively collects their axioms. Only `propext`, `Classical.choice`, and
`Quot.sound` occur. The audit also checks independent object/hom universes,
the unchanged actual joint map and ambient biproduct source, the minimal
nonabelian cokernel-membership endpoint, the actual relative cofibration,
and its ordinary inherited-pushout consumer. The audit is warning-free.

No frozen source was changed. The author's initial audit's biproduct equality
needed parentheses for parsing; the separate independent audit includes
that correction without changing either accepted source.

## Evidence

- Frozen manifest: `logs/cylinder-subcategory-sources.sha256`
- Independent manifest and build/audit/hash/import-resolution evidence:
  `logs/cylinder-subcategory-independent-20261009/`
- Independent consumer and origin audit:
  `audits/CylinderSubcategoryIndependentAudit.lean`

Manifest SHA-256:
`b854f31f5da074753d181183319ba191ed56fe8001024e4de9830954f9938803`.

This accepts the actual inherited cylinder calculations. It does not assert
Waldhausen additivity, a fibration theorem, or Gillet–Waldhausen.
