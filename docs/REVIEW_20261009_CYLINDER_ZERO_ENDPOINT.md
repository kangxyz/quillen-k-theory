# Independent review: actual zero-source cylinder endpoint

Accepted 2026-10-09 06:11 UTC after full semantic inspection, fresh isolated
rebuild, fixed-count recursive axiom audit, independent-universe actual-map
consumers, and pre/post source rehashes.

## Accepted mathematical scope

`Quillen/Waldhausen/Cylinder/ZeroEndpoint.lean` proves that the identity cone
of an actual zero complex is zero, degreewise using the original cone terms.
Consequently the original cylinder projection `Cone(id K) ⊞ L → L` is an
actual isomorphism whenever `K` is zero. Its inverse is exactly the original
second biproduct inclusion. The two inverse equations are proved using the
actual biproduct universal property and vanishing of the cone summand.

For any category-indexed family of arrows with genuinely zero source objects,
the original cylinder projection is a natural isomorphism to the original
target family. Naturality is the previously proved original cylinder
naturality. Neither the indexing category nor its morphisms are restricted
to a groupoid or to weak equivalences. No literal equality with the chosen
zero object, strict normalization, cylinder theorem, or fibration equivalence
is asserted or assumed.

No issue was found in the statement, proof, imports, or semantic contract.

## Independent verification

The source was rebuilt into a separate artifact overlay that excludes the
live source-origin artifacts. The new olean is an actual fresh file, and the
audit's `--deps` output resolves that exact artifact. Previously accepted
imported dependencies were reused; inspected dependency sources rehash
unchanged afterward. The frozen source was never modified.

`audits/CylinderZeroEndpointIndependentAudit.lean` checks exactly 10
source-origin declarations, including private/generated declarations, with
recursive axiom collection. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed. Consumer checks retain independent ambient object/hom universes
and independent indexing-category object/hom universes. They verify the actual
projection and target section, both original natural transformations, the
original composite inverse equation, and applicability to any genuine zero
source rather than only the chosen zero object. All checks are warning-free.

## Evidence

- Frozen author manifest: `logs/cylinder-zero-endpoint-sources.sha256`
- Independent source/axiom/consumer/import-resolution/hash evidence:
  `logs/cylinder-zero-endpoint-independent-20261009/`
- Independent audit: `audits/CylinderZeroEndpointIndependentAudit.lean`

Frozen manifest SHA-256:
`a563f780b63259feab45c01d69215f68418b4339924548c995d1e9d7861423d1`.
