# Complete original-map weakness from finite cube-boundary RLP

## Checked source scope

`Quillen/Topology/CubicalSubdivision/BoundaryWeakEquivalence.lean` compiles
warning-free and is frozen. Its fixed-6 recursive defining-origin audit and
all 16 exact consumers passed warning-free at 11:43:43 UTC on 2026-10-09,
with source and prerequisite hashes unchanged. Independent fresh review is
being performed separately. The source is
SHA256 `d37154ca1376590c4b8bfc7eaf7e611da3a5459ce88107c3139dda076a4a9930`.

Manifest: `logs/boundary-weak-equivalence-sources.sha256`, fingerprint
`8f0bbceb69f5b336c5d1243e2d4bf8d76ea8b072358eae7d39d32af382d65f7d`.
All accepted boundary, local-lifting and cubical test sources remain unchanged.

## Exact endpoint

For a continuous map `f : C(E,F)` with arbitrary independent source and target
universes and their given topologies,
`CubicalSubdivision.BoundaryLifting.isWeakHomotopyEquivalence` proves the
repository's complete `IsWeakHomotopyEquivalence f` from actual finite
cube-boundary RLP of f. The conclusion uses the original map, original finite
`GenLoop` quotients and their actual `homotopyGroupMap` in every degree,
including zero. It separately supplies component surjectivity.

The zero-dimensional strict lifting test proves the stronger statement
`BoundaryLifting.surjective`: f is actually point-surjective. Its boundary is
genuinely empty and the target zero-cube map is constant at the specified
point. Thus no nonempty-source assumption or vacuous-basepoint loophole is
present.

## Exact boundary and cylinder tests

`BoundaryLifting.presentation` transports only the test parameters along the
proved actual boundary homeomorphism. It returns a strict lift for the
original canonical presentation, preserving both the entire specified
boundary map and the exact equation after applying f. The parameter lift may
live in a third arbitrary universe w, independent of E and F.

`BoundaryLifting.cylinder` uses the definitional equality between the next
canonical presentation and the actual side/caps pushout `CylinderBoundary`.
Its map is the original cylinder-boundary map followed by `stepHomeomorph`,
which adds the first coordinate. A strict (n+1)-cube lift therefore gives a
strict lift on the actual n-cube cylinder, again preserving the entire
boundary map and original target equation. No HEP or lifting assertion for
an arbitrary compact pair is introduced.

## Original finite homotopy-set maps

Surjectivity lifts an original target loop representative on the n-cube with
constant source basepoint on its whole boundary. The strict boundary equation
makes the lift a genuine source `GenLoop`; its postcomposition by f is the
original target representative exactly, so the original quotient class is
in the image.

Injectivity starts with the actual relative homotopy supplied by equality
of the two original image classes. The source boundary map is assembled by
the genuine pushout: one cap is the first loop, the other is the second,
and the entire side cylinder is the constant source basepoint. Their gluing
uses their original loop boundary conditions. The target cylinder map is the
original relative homotopy. Its strict square is checked on both caps and
on every side point via the actual joint-surjectivity of that pushout.

The strict (n+1)-cube lift has exactly the original two loops as its endpoint
maps. Full coverage of the original n-cube boundary gives constancy on every
boundary point at every time. It is therefore an actual relative homotopy
of the source loop representatives, and `Quotient.sound` gives equality of
the original source classes. This proof is uniform at n=0 and uses no group
law for the zero-dimensional homotopy set.

The pushout into E is formed in E's universe. The target map into F is an
ordinary continuous map and its square is proved pointwise, so no equality
of the source and target universes is silently required.

## Consumers and limits

The own audit includes combined `Quillen.Library`, actual defining-origin
recursive axiom inspection, and 16 consumers. They check point and component
surjectivity; the original homotopy-set maps in all finite degrees and
explicit degree zero; empty-source consequences; full strict presentation
and cylinder data with an independent parameter universe; actual categorical
boundary-RLP input; actual open-restriction locality; original mapping-path
fiber and relative-row endpoints; and recovery of the original f from its
endpoint using the genuine mapping-path inclusion homotopy equivalence.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed recursively.

The local-cover consumer assumes strict boundary RLP for the literal
restrictions of f over the cover. It does not replace that input by a
mapping-path construction over a chart that forbids paths leaving the chart.
For the row consumers, the existing category model has the explicit common
object/hom universe required by that model.

This theorem is a direct finite-test-to-weakness result. It neither infers
full HELP on arbitrary compact HEP pairs nor supplies the still-separate
controlled collar lifts or global weak-cartesian gluing theorem.

Audit: `audits/BoundaryWeakEquivalenceAudit.lean`.
Checks: `logs/check-boundary-weak-equivalence.sh` and
`logs/audit-boundary-weak-equivalence.sh`, using one Lean thread under slot1.
Evidence: `logs/boundary-weak-equivalence-20261009/`.
