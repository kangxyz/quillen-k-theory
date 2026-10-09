# Normalized based naturality of the canonical Q/S equivalence

Sources: `Quillen/Waldhausen/QuillenComparison/ZeroNormalization.lean` and
`Quillen/Waldhausen/QuillenComparison/BasedNaturality.lean`.
Manifest: `logs/qs-based-naturality-sources.sha256`.

## Proved endpoints

For a genuine exact functor F between categories in a common object universe
and a common hom universe (with these two universes independent):

- `comparisonKEquiv_naturality` proves that the canonical Q/S equivalence
  commutes with `normalizedExactSKMap F` and the existing `ExactFunctor.KMap F`
  in every natural-number K-degree. No strict-zero hypothesis or target square
  is among its inputs.
- `normalizedExactSKMap` is definitionally induced on actual homotopy groups
  by postcomposing S-diagrams with the zero-rebased original functor. It is not
  defined by transporting the Quillen K-map through the desired equivalence.
- `normalizedExactSKMap_eq_KMap` identifies it with the existing
  `Waldhausen.KMap` whenever the ordinary structural `Waldhausen.IsExact`
  witness is supplied.
- `comparisonKEquiv_naturality_KMap` consequently proves the square for the
  two original K-map APIs, with their actual chosen-zero normalization.

## Genuine normalization and proof

`zeroNormalized` transports additivity through the actual natural isomorphism
from F to its objectwise rebasing. Every conflation is transported using the
three component isomorphisms of its mapped short complex. The resulting functor
is therefore genuinely exact and sends the specified source zero exactly to
the specified target zero. The existing based natural-isomorphism invariance
of Quillen K-maps proves `zeroNormalized_KMap`.

For strict zero preservation, the canonical zero-object isomorphism is exactly
equality transport, so the Quillen normalization changes no functor. Literal
postcomposition preserves the constant zero simplex in every degree, including
the subdivided source. The frozen raw simplicial comparison naturality and
endpoint naturality give based commuting squares on actual homotopy groups.
Surjectivity of the proved subdivision endpoint K-equivalence then gives the
comparison square. Applying this to the normalized exact functor proves the
unconditional result.

For agreement with `Waldhausen.KMap`, uniqueness of maps into the actual target
zero identifies the two supplied zero isomorphisms. The underlying normalized
S-maps are equal. An explicit equality-transport elimination lemma identifies
`groupsMapOfZeroEq` with its actual based `piMap`, so no unbased homotopy is
incorrectly used in place of a based one.

## Verification and scope

Both implementation sources compile without warnings or errors. All 45 origin
declarations, including private/generated declarations, passed recursive axiom
collection with only `propext`, `Classical.choice` and `Quot.sound`.
`audits/QSBasedNaturalityAudit.lean` is count-frozen at 45 and checks arbitrary-
universe exact-map consumers, the strict-zero and unconditional squares, and
agreement with the existing Waldhausen K-map. Logs are
`logs/qs-zero-normalization.log`, `logs/qs-based-naturality.log`, and
`logs/qs-based-naturality-audit.log`.

This scope does not itself derive the full structural Waldhausen exactness
witness from the Quillen exact-functor data. That separate adapter needs
preservation of arbitrary pushout squares along inflations, beyond the
zero-corner cokernel squares already used by S-diagrams. No such witness is
required for the unconditional normalized S-map theorem. Prior frozen sources
and public definitions were not changed.
