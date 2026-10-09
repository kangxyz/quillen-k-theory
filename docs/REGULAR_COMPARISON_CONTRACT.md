# Regular-scheme K-to-G comparison: mathematical contract

Current status: the full canonical comparison for every regular affine ring
is proved, without a finite-dimension assumption. The remaining geometric
target is the non-affine theorem with a genuine resolution-property argument.

Audit date: 2026-10-09. Pinned mathlib: 5ed2965256430c3649e86755f9576b54eca72435.

The comparison to prove is the existing canonical `Quillen.Scheme.KToG`,
induced by the exact inclusion of finite locally free sheaves into coherent
sheaves. A comparison for a newly introduced perfect-complex theory is a
separate result and does not replace this map.

## Primary-source contract

* [Stacks, Tag 066Z](https://stacks.math.columbia.edu/tag/066Z): every finite
  module over a regular (Noetherian) ring has a bounded resolution by finite
  projectives. The bound may depend on the module. The proof uses finite-free
  syzygies, openness of the free locus, local regularity, and quasi-compactness.
  **Finite Krull dimension is not needed for this objectwise statement.**
* [Stacks, Section 10.110](https://stacks.math.columbia.edu/tag/065U): a regular
  local ring has global dimension equal to its Krull dimension. For a general
  Noetherian ring, regularity plus finite Krull dimension gives a uniform
  finite global-dimension bound. Regular Noetherian rings can have unbounded
  dimension, so the uniform and objectwise statements must be distinguished.
* [Stacks, Tag 0FDC](https://stacks.math.columbia.edu/tag/0FDC): on a regular
  scheme, bounded coherent complexes are perfect. On a quasi-compact regular
  scheme the converse also holds. Local perfection alone does not provide
  globally defined finite locally free terms.
* [Stacks, Section 36.36](https://stacks.math.columbia.edu/tag/0F85): the
  resolution property requires a finite locally free sheaf surjecting onto
  each finite-type quasicoherent sheaf. An ample invertible sheaf, or an ample
  family, supplies it. [Tag 0F8A](https://stacks.math.columbia.edu/tag/0F8A)
  supplies it for quasi-compact regular schemes with affine diagonal; separated
  regular Noetherian schemes are an important special case.
* [Stacks, Section 36.37](https://stacks.math.columbia.edu/tag/0F8D): on a
  quasi-compact quasi-separated scheme with the resolution property, perfect
  complexes admit bounded finite locally free representatives. Applying
  finite-free-cover/syzygy induction to a coherent sheaf produces the finite
  admissible resolutions needed for Quillen's resolution theorem.

Thus suitable genuine geometric targets include regular Noetherian schemes
with the resolution property, or quasi-compact regular schemes with affine
diagonal. Do not silently assert global vector-bundle resolutions from
regularity alone, and do not assume a common finite dimension when only
objectwise finite resolutions are needed.

## Pinned-library audit

Present:

* `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing` via maximal
  ideal generator dimension; `IsRegularRing` via all prime localizations;
  fields and Dedekind domains as instances.
* `Mathlib.CategoryTheory.Abelian.Projective.Dimension`: Ext-defined projective
  dimension and short-exact-sequence dimension shifting.
* `Mathlib.RingTheory.LocalProperties.ProjectiveDimension`: a fixed finite
  module's projective dimension is bounded by `n` exactly when every prime
  (or maximal) localization has that bound.
* `Module.exists_finite_presentation`: an actual finite free surjection.
* `Mathlib.LinearAlgebra.FreeModule.PID`: finite free submodule theorem.

Missing after source search:

* The regular-local-ring finite-global-dimension theorem (Auslander–Buchsbaum–
  Serre). `RegularLocalRing/Defs` even lists localization of regular local
  rings as a TODO.
* A geometric regular-scheme predicate with the above finite-resolution
  bridge, and the general global resolution-property construction.

The new finite-projective-resolution helpers prove genuine intermediate
algebraic statements. They must not be described as a completed general
regular-scheme comparison while these missing steps remain.

## Verified implemented endpoints

`Quillen/Scheme/Regular/SmallComparison.lean` proves, for every commutative
principal ideal domain `R` and every nonnegative `n`:

* `Quillen.Scheme.KToG_pid_bijective R n`;
* `Quillen.Scheme.KToGPIDEquiv R n`;
* `Quillen.Scheme.KToGPIDEquiv_toMonoidHom R n`, identifying its forward map
  with the existing `Scheme.KToG (Spec R) n` by reflexivity.

There are no extra projective-dimension, resolution, or K-equivalence
hypotheses on these PID endpoints. A separate field-spectrum endpoint is in
`Regular/Field.lean`.

The proof uses actual finite-free module surjections and the PID submodule
basis theorem, yielding length-one finite-free resolutions. `AffineProjective`
proves both directions of finite projective module / finite locally free
associated-sheaf comparison. `AffineResolution` transports actual resolutions
through the affine coherent/module equivalence. `SmallComparison` explicitly
factors the canonical small-model comparison through an inherited exact
subcategory, proves the first factor an exact equivalence, and applies the
proved Quillen length-one resolution theorem to the second factor.

`finiteProjectiveResolution_length_le` and
`coherentResolution_length_le_of_projectiveDimensionLE` additionally produce
actual finite resolutions from mathlib's independent Ext-vanishing bounds.
These are genuine intermediate theorems; the missing general
regularity-to-finite-projective-dimension implication is not assumed away.

## Genuine regularity endpoint in dimension at most one

`Regular/AffineLowDimension.lean` additionally proves
`Quillen.Scheme.KToG_regular_dimension_le_one_bijective` and
`Quillen.Scheme.KToGRegularDimOneEquiv` under exactly the existing
`IsRegularRing R` class and `ringKrullDim R ≤ 1`, in every nonnegative degree.
The forward homomorphism is again definitionally the existing canonical
`Scheme.KToG`. No domain, PID, finite-projective-dimension or finite-resolution
hypothesis appears in this endpoint.

The needed local algebra is proved in `Regular/LocalPrincipalDomain.lean` and
`Regular/LocalLowDimension.lean`. Krull intersection yields a power-of-parameter
factorization with unit coefficient for every nonzero element of a noetherian
local ring with principal maximal ideal. Positive dimension excludes a
nilpotent parameter, which proves the domain property. Dimension-zero
regularity directly forces the maximal ideal to vanish. The cotangent-space
form of regularity then identifies every local ring of dimension at most one
as a PID. Prime-localization of projective dimension carries the resulting
bound back to the original regular ring; actual finite resolutions and the
previous canonical comparison complete the proof.

This fully discharges regularity-to-resolution for the affine
low-dimensional endpoint. The arbitrary-dimensional regular-ring theorem and
the general non-affine geometric resolution-property argument are still
separate open steps.

## Arbitrary finite dimension, now proved from regularity

The previously missing local-regularity implication has now been proved in
`Algebra/RegularLocal/{ParameterAvoidance,ParameterQuotient,Domain,Parameters,
QuotientLifting,ProjectiveDimension}.lean`. A minimal-parameter quotient,
prime-avoidance/Nakayama domain induction, and finite-free syzygy lifting
provide the actual projective-dimension bound in every finite local dimension.

`Scheme/Regular/AffineFiniteDimension.lean` therefore proves
`Scheme.KToG_regular_dimension_le_bijective` and
`Scheme.KToGRegularFiniteDimensionEquiv` for every regular ring with a given
finite dimension bound. `KToG_regular_finiteDimension_bijective` uses the
standard `FiniteRingKrullDim` typeclass instead. No extra finite-PD,
resolution or K-theory assumption occurs in these endpoints; the equivalence's
forward homomorphism is definitionally `Scheme.KToG`.

The open steps are now objectwise compactness for possibly unbounded-dimensional
regular rings and the genuine global resolution-property argument for
non-affine schemes. The pinned-mathlib audit above describes what was absent
upstream before these new proofs were supplied, not an unresolved local gap.


## Full regular-affine endpoint, including unbounded Krull dimension

`Algebra/RegularLocal/GlobalProjectiveDimension.lean` now proves
`CoherentScheme.projectiveDimension_ne_top_of_regular` from `IsRegularRing`
alone. Its actual finite-free syzygy modules have increasing open free loci;
local regularity makes them cover the prime spectrum. Compactness yields a
bound for each original finite module, not a common bound for the ring.

`Scheme/Regular/Affine.lean` therefore proves:

* `Scheme.KToG_regular_affine_bijective R n`, under only `IsRegularRing R`;
* `Scheme.KToGRegularAffineEquiv R n`;
* `Scheme.KToGRegularAffineEquiv_toMonoidHom R n`, by reflexivity to the
  existing canonical `Scheme.KToG (Spec R) n`;
* `Scheme.KToGRegularAffineEquiv_restrict`, retaining actual geometric
  open-restriction naturality.

All degrees are covered. No finite Krull-dimension, domain, PID, finite-PD,
finite-resolution or assumed K-equivalence hypothesis is added to these
endpoints. The earlier low-dimensional and finite-dimensional theorems remain
valid special cases. Non-affine vector-bundle K-theory still requires the
proper global resolution-property argument, as explained in the source
contract above.
