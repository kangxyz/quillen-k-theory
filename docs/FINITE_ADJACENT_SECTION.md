# Canonical representatives at arbitrary finite coordinates

Checked source: `Quillen/Algebra/FiniteAdjacentSection.lean`.
It uses an arbitrary actual `CommGroup G` and the unchanged original Euler
and incidence homomorphisms in `FiniteAdjacentComplex`. There are no K-theory
or fibration inputs.

## Exact APIs

- `singleCoordinate G i` is definitionally the original `MonoidHom.mulSingle`;
  its value is literally `Pi.mulSingle i x`.
- `coordinateSign G k` is identity for even `k` and inversion for odd `k`, as
  an automorphism of the existing group.
- `euler_singleCoordinate G i x` identifies Euler on the original single
  coordinate with this automorphism. `euler_singleCoordinate_bijective G i`
  proves bijectivity of that actual composite.
- `coordinateSection G n i` is the single-coordinate inclusion composed with
  inverse sign. `euler_coordinateSection` proves it is an actual section.
- `coordinateValue G n i y` is explicitly Euler of `y` at an even index and
  its inverse at an odd index. `coordinateRepresentative` is literally
  `Pi.mulSingle i (coordinateValue G n i y)`.
- `existsUnique_incidence_representative` proves there is a unique original
  disk tuple `d` with `incidence d * coordinateRepresentative y = y`.
- `existsUnique_coordinateValue` proves uniqueness of the supported coefficient
  modulo the original incidence image.
- `existsUnique_incidence_coordinate` proves uniqueness of the full pair
  `(d,c)` satisfying `incidence d * Pi.mulSingle i c = y`.

These statements cover every `i : Fin (n+1)`, including the sole coordinate
when `n=0`. Thus an absolute degree zero occurring inside an interval beginning
negatively may be represented by its actual finite coordinate, without requiring
it to be the initial term. Sign is relative to the first tuple coordinate.
The theorem does not itself identify a particular K-theory map with incidence.

## Proof

Single-coordinate tuples satisfy the literal zero/successor recurrences under
`Fin.cons`. Induction through the original Euler recurrence identifies the
restricted map with alternating identity/inversion. Its inverse gives the
explicit section and coefficient. The quotient of an arbitrary tuple by its
representative has unit Euler product; the accepted core kernel/image theorem
gives an original incidence preimage. Core incidence injectivity makes that
preimage unique. Applying original Euler to any competing decomposition forces
the same coefficient, proving full uniqueness.

## Frozen verification

Source SHA-256:
`4ac5ddb7d240a3fa9206180fa4b4f829d6536738966978828c4031e757d01dbd`.
Manifest: `logs/finite-adjacent-section-20261009/sources.sha256`.
Manifest SHA-256:
`ab0e9ef5bdd19f982c6d2f04c8d5de456af337958b2d9eb0f08e4c3524964d83`.

The final source check (`check2.log`) and fixed23 recursive-origin audit
(`audit-final.log`) passed warning-free. The audit includes generated/private
origins and finds only `propext`, `Classical.choice`, and `Quot.sound`.
Seventeen actual-map consumers cover the literal coordinate inclusion,
even/odd formulas, original incidence multiplication, section identity,
off-coordinate unit support, complete uniqueness, and explicit length-one
and odd-coordinate cases. Both new-section and unchanged-core hashes match
before and after the audit.

Audit: `audits/FiniteAdjacentSectionAudit.lean`.
Evidence and exact artifact hashes: `logs/finite-adjacent-section-20261009/`.
Checks use the logged shared slot1. This is author verification; independent
review of this new module remains separate. The unchanged core has its own
independent acceptance in `docs/REVIEW_20261009_FINITE_ADJACENT_COMPLEX.md`.
