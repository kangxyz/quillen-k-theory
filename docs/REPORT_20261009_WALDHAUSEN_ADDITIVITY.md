# Genuine realized Waldhausen additivity

## Checked endpoint

Import `Quillen.Waldhausen.Additivity.RealizedAdditivity`.
In `Quillen.Waldhausen.Additivity`, for actual Waldhausen structures `V` and
`W`, exact functors `F,G,H`, and a genuine structural cofibration sequence
`hs : IsCofibrationSequence V W a b`:

- `deloopingMap_additivity V W a b hs` proves that the original realized
  S-map of `G` is homotopic to the original realized S-map of `H ⨿ F`.
- `additivityHomotopy V W a b hs` supplies an actual continuous homotopy
  with those exact endpoints.
- `bisimplicial_additivity` is the corresponding independent-grid endpoint.

The categories have arbitrary shared object/hom universe levels. No
preadditive, abelian, balanced, saturation, cylinder, or fibration hypothesis
is imposed. The chosen binary-coproduct instance in the endpoint is available
from `hasBinaryCoproducts W`, proved using Waldhausen zero pushouts.

`IsCofibrationSequence` contains only the three functors' genuine structural
exactness, pointwise cofiber pushout squares, and the usual relative-cofibration
condition on `a`. It contains no K-theory, realization, or equivalence assertion.

**This endpoint is explicitly unbased.** It does not yet identify the canonical
chosen-zero K-homomorphisms or assert a fixed chosen-zero track.

## Actual proof constructions

1. `pushoutFunctor` sends an arrow `X → Y` to the actual pushout
   `G(X) ⨿[F(X)] F(Y)`, functorially on every commutative square.
2. Gluing proves weak-equivalence preservation. Two actual cobase-change
   factorizations prove cofibration preservation. Finite pushout interchange
   proves preservation of the displayed quotient squares without assuming
   global cocompleteness. Zero objects and all genuine S-diagram conditions
   are retained.
3. Equal interval restrictions yield the middle-functor endpoint. Separated
   restrictions yield actual zero arrows, proved by factorization through a
   zero diagonal. Their pushouts are naturally isomorphic to the quotient on
   the first restriction plus the subobject on the second restriction.
4. `mixedDeformationMap` is the actual bisimplicial deformation. It is strictly
   natural in the independent interval and nerve directions, including all
   endpoint-changing ordinal maps. Its zero/one restrictions agree exactly
   with the checked identity/separated auxiliary maps.
5. Both endpoint isomorphism families have proved componentwise reindex
   coherence. The genuine nerve-direction cylinder turns these families into
   simplicial homotopies, retaining the actual endpoint maps.
6. The checked minimum-cut contraction relates the two realized endpoints.
   Applying the same construction to the genuinely constructed split sequence
   gives a common endpoint. The proved ordinary-subdivision realization
   equivalence cancels the source. Finally, the exact diagonal identification
   transports the result to the unchanged original `deloopingMap`.

The deformation follows the pushout approach to additivity, with the mixed
cylinder handled by an explicit simplicial retraction rather than an assumed
cylinder homeomorphism. Background: Daniel Grayson,
[The Additivity Theorem in Algebraic K-Theory](https://ems.press/content/serial-article-files/26118).

## Verification and frozen boundary

- Twenty implementation sources are frozen in
  `logs/additivity-realized-sources.sha256`.
- Manifest fingerprint:
  `a88eb0a9b459884ae34251a73e2c24a6679e145e8d9d21fe3f7555b22b97d044`.
- `audits/AdditivityRealizedAudit.lean` recursively inspected every declaration
  from all twenty defining modules: **249 declarations**, with only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Audit and arbitrary-universe consumers passed in
  `logs/additivity-realized-audit.log`. An actual bounded-acyclic truncation
  cofibration sequence also instantiates the continuous additivity homotopy.
- All frozen hashes revalidated in
  `logs/additivity-realized-hash-recheck.log`.
- The final endpoint sources compile warning-free. Four existing `letI`
  style warnings remain in the first two algebra modules; no proof warning,
  placeholder, or nonstandard axiom remains.
- The initial eleven algebra sources were independently rebuilt and reviewed:
  `docs/REVIEW_20261009_ADDITIVITY_ALGEBRA.md`. Independent review of the
  subsequent frozen deformation and final endpoint boundaries is coordinated
  separately; it is not inferred from the implementation audit.

The separately frozen Q/S comparison sources are unchanged.

## Exact remaining work

1. Normalize the internal pushout and common endpoint functors at the chosen
   zero, prove that the actual deformation is fixed there, and identify the
   resulting equality with the existing canonically rebased `KMap` definitions.
2. Apply functor additivity to a genuine extension category and its internal
   source/identity/quotient sequence, then prove the product comparison needed
   for an extension-category additivity equivalence.
3. Prove the change-of-weak-equivalences fibration and the remaining
   Gillet–Waldhausen argument. Neither is supplied as an input or claimed here.

New chosen-zero normalization modules are outside this frozen twenty-source
boundary until separately checked and audited.
