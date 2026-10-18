# Perfect-complex candidates

## Local candidate interfaces

These local candidate implementations extend the pinned Aglib strict/local perfect interfaces.
They retain actual sheaf cochain complexes and chain maps, derived localization, term and
cohomological bounds, and the original object/hom universes. Existing declaration namespaces are
preserved.

The root provides extension/kernel closure, strict and flat geometric pullback, finite flat direct
image under its stated local noetherian hypotheses, coherent homology, actual scalar and line
tensor operations, and derived perfect-object comparisons. `Affine/`, `Support/`, `OpenGluing/`,
and the two derived-image directories provide the actual affine/roof/gluing and qcqs complement
theory. `GlobalDensity` and `GlobalSupportedDensity` give extension up to an actual derived retract
and perfect complement under their displayed quasi-compact, quasi-separated and compact-open
conditions. None of these statements silently replaces the original complex by a strict global
model on a general scheme.

Waldhausen structures, K/G/Q/S constructions, scalar K-cofiber/additivity protocols and
projective-line/curve applications remain downstream in Quillen.

## Remaining comparisons

- General-source perfect preservation by derived direct image, unrestricted unbounded derived pushforward, and general bounded-below flat-base-change invertibility.

- Strict/local equivalence on arbitrary nonaffine schemes and perfect pullback on arbitrary non-quasi-compact schemes.
