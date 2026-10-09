# Independent review: regular-local algebra and canonical regular-affine K-to-G

Reviewed on 2026-10-09 independently of the implementation author. This review
does not change proof sources, public facades, configuration, or verification
scripts. The finite-dimensional subcase and the unrestricted affine endpoint
are distinguished below. General nonaffine resolution-property results and
perfect-complex comparison theorems are outside this review.

## Exact mathematical contracts

The pinned mathlib definition `IsRegularLocalRing R` extends `IsLocalRing R`
and `IsNoetherianRing R`; its additional field equates the maximal ideal's
minimal generator count with `ringKrullDim R`. It does not assume a domain,
regular sequence, finite projective dimension, or a resolution. The local
dimension is automatically a natural number under this definition.

The following are genuine conclusions under that definition:

- `RegularLocal.isDomain_of_regularLocal R`: the ring is a domain.
- `RegularLocal.exists_regular_parameter R d hd`: when the dimension is
  `d + 1`, there is an element of the maximal ideal that acts injectively on
  `R`, and whose quotient is regular local of dimension exactly `d`.
- `RegularLocal.hasProjectiveDimensionLE_of_regularLocal_dimension d R hd M`:
  every finite module `M : ModuleCat.{u} R` has projective dimension at most
  `d`, when `ringKrullDim R = d`.
- `RegularLocal.finiteProjectiveResolution_of_regularLocal R M`: an actual
  finite admissible resolution by finite projective modules exists.

Mathlib's `IsRegularRing R` means a noetherian commutative ring whose
localization at every prime ideal is regular local. It imposes no uniform
finite Krull-dimension bound.

The first affine endpoint
`Scheme.KToG_regular_finiteDimension_bijective R n` assumes only
`R : CommRingCat.{u}`, `[IsRegularRing R]`, `[FiniteRingKrullDim R]`, and
`n : ℕ`. Its explicit-bound version instead assumes
`d : ℕ` and `ringKrullDim R ≤ d`. The finite-dimension typeclass includes
nonemptiness of the spectrum; the explicit-bound theorem does not need that
extra assumption.

The unrestricted endpoint `Scheme.KToG_regular_affine_bijective R n` assumes
only `R : CommRingCat.{u}`, `[IsRegularRing R]`, and `n : ℕ`. It concludes
bijectivity of the existing `Scheme.KToG (Spec R) n`. In particular it has no
assumed finite dimension, finite projective dimension, resolution property,
categorical contraction, or K-equivalence.

`Scheme.KToGRegularAffineEquiv R n` is a multiplicative group equivalence
whose forward homomorphism is definitionally that same original canonical
map. Its open-restriction naturality is the existing geometric naturality
of `Scheme.KToG`, not a comparison with an independently chosen inverse.

## Semantic source review

### Parameters and domain induction

`ParameterAvoidance` first excludes containment of the maximal ideal in its
square using finite generation and Nakayama. It separately excludes its
containment in any minimal prime using maximal-ideal height. Finiteness of
minimal primes permits prime avoidance with the square as its sole nonprime
exception. This produces an element outside both the square and every
minimal prime.

`ParameterQuotient` extends the resulting nonzero cotangent vector to a
basis, lifts that basis while retaining the specified parameter, and uses
Nakayama to generate the actual maximal ideal. Removing the parameter
gives the quotient's generator bound. The opposite dimension inequality
comes from the principal-ideal height bound. Thus quotient regularity and
the exact dimension drop are proved before any domain hypothesis is used.

`Domain` inducts on that finite dimension. The quotient is a domain by the
induction hypothesis, so the principal ideal is prime. For a minimal prime
below it, primality and avoidance imply that every element is the parameter
times another element of that same minimal prime. Nakayama makes this prime
zero, proving the ring is a domain. `Parameters` then derives scalar
regularity of the chosen nonzero parameter.

These conclusions agree with [Stacks 00NN](https://stacks.math.columbia.edu/tag/00NN).
The domain proof uses an elementary alternative to that page's associated-
graded argument; its separate inputs are [prime avoidance, 00DS](https://stacks.math.columbia.edu/tag/00DS)
and [Nakayama, 00DV](https://stacks.math.columbia.edu/tag/00DV).

### Actual resolutions and local projective dimension

`QuotientLifting` defines the actual quotient-by-scalar linear maps over the
quotient ring and constructs the corresponding short complex. Its proof of
short exactness requires regularity on the quotient term; it does not assume
that tensoring arbitrary short exact sequences remains left exact.

The induction starts with the standard finite-presented freeness-lifting
theorem over a local ring. In the successor step it takes a genuine finite
free cover with finite kernel, restricts scalar injectivity from the free
middle term to the kernel, reduces the exact sequence, and decreases the
quotient projective-dimension bound. The result is a real finite conflation
tower, not merely an asserted numerical bound. A separate induction on
that tower proves the stated Ext-defined projective-dimension bound.

For an arbitrary finite module, taking the first finite-free syzygy supplies
the regularity needed on the resolved module, costing one step. Combining
this operation with the proved regular-parameter quotient and the field
base case gives `ProjectiveDimension`'s local dimension induction.

`AffineFiniteDimension` transports the local bound using the height bound
on each prime localization and mathlib's finite-module local-to-global
projective-dimension theorem. Every homological assumption in its final
finite-dimensional regular-affine endpoint is therefore discharged.

### Objectwise compactness without a global dimension bound

`GlobalProjectiveDimension` selects actual finite-free covers and iterates
their finite kernels. Localized short exact sequences prove that the
original module has localized projective dimension at most `n` exactly
when the `n`th syzygy is projective at that prime. Finite projectivity over
the local ring is equivalent to freeness, using an explicit linear
equivalence between the two localized-module models.

The free locus of each syzygy is open because the syzygy is finitely
presented. The projective-dimension characterization proves that these
opens increase and cover the spectrum. Compactness of the affine spectrum
gives one index covering all primes for this fixed module. The primewise
local-to-global theorem then supplies a global finite projective-dimension
bound for that module. Different modules may require different indices;
no common bound on all modules or all local-ring dimensions is inferred.

This is the finite-syzygy/free-locus argument of
[Stacks 066Z](https://stacks.math.columbia.edu/tag/066Z), implemented through
the already-proved regular-local bound. The final finite-projective
resolutions retain actual admissible maps and the original augmentation.

### The original K-to-G map

`GeneralComparison` carries these actual resolutions to coherent sheaves
under the affine exact equivalence, retaining the original resolved object
through its unit isomorphism. It transports them to the chosen small model
with no uniform length bound. The previously reviewed exact equivalence
between vector bundles and their inherited full subcategory supplies the
other factor of the canonical comparison.

The independently accepted full objectwise-finite Quillen resolution
theorem then proves bijectivity of the inherited inclusion map. The
factorization `vectorBundleSmall_factor` and `ExactFunctor.KMap_comp`
identify its composite with the original inclusion-induced scheme map.
The final equivalences are defined directly with that map using
`MulEquiv.ofBijective`; forward-map and pointwise equality checks use `rfl`.

The full resolution theorem's independent review remains
`docs/REVIEW_20261009_FULL_RESOLUTION.md`; the geometric affine adapter's
earlier review is `docs/REVIEW_20261009_CANONICAL_PID_K_G.md`. Neither a
perfect-complex comparison nor a new global geometric resolution property
is an assumption of the affine result reviewed here.

## Verification

The independent focused current-source command was:

```
lake --rehash build Quillen.Scheme.Regular.AffineFiniteDimension Quillen.Scheme.Regular.Affine
```

It passed with 3,478 jobs on Lean 4.34.0 and pinned mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. All ten reviewed new modules were
actually rebuilt. Only style and unused-section-variable warnings occurred.
Log: `logs/regular-algebra-independent-build.log`.

Independent all-origin axiom audits and arbitrary-universe consumer
examples are in `audits/RegularAlgebraIndependentAudit.lean` and
`audits/RegularAffineIndependentAudit.lean`. The audits select declarations
by defining module, including private and generated constants, and traverse
their transitive axiom dependencies.

The finite-dimensional/algebra audit passed all **70 declarations in eight
modules**, with only `propext`, `Classical.choice`, and `Quot.sound`. The
per-module counts are ParameterAvoidance 2, ParameterQuotient 5, Domain 3,
Parameters 2, QuotientLifting 22, ProjectiveDimension 4, GeneralComparison 3,
and AffineFiniteDimension 29. Its arbitrary-universe domain, regular
parameter, local-projective-dimension, and original-KToG consumer examples
all compile; equivalence forward-map and pointwise identities are `rfl`.
Log: `logs/regular-algebra-independent-all-axioms.log`.

**Finite-dimensional/algebra acceptance: passed.**

The unrestricted-affine audit passed all **65 declarations in two modules**:
GlobalProjectiveDimension 36 and Affine 29. Every transitive axiom is again
one of `propext`, `Classical.choice`, and `Quot.sound`. The arbitrary-universe
finite-projective-dimension and actual-resolution consumers, the endpoint
assuming only `IsRegularRing`, both forward-map `rfl` identities, and the
geometric open-restriction consumer all compile. Log:
`logs/regular-affine-independent-all-axioms.log`.

The initial unrestricted-affine audit run passed the complete 65-declaration
axiom traversal but one separately added algebra-consumer example lacked a
local `Abelian.hasFiniteBiproducts` instance. Adding the same local instance
used in the sources corrected only the audit harness. The complete rerun
exited successfully with no warnings or errors; no library proof changed.
The initial harness diagnostic is preserved separately as
`logs/regular-affine-independent-audit-harness-first.log`.

**Unrestricted regular-affine acceptance: passed.** Together the two audits
cover **135 declarations in ten new source modules**. The accepted full
resolution theorem's fourteen existing frozen hashes also still match;
see `logs/regular-affine-independent-resolution-hash-check.log`.

The source-token audit passed without proof placeholders or custom
assumptions: `logs/regular-algebra-independent-source-token-audit.log`.

Frozen source manifests:

- Eight regular-local/finite-affine files, 699 lines:
  `logs/regular-algebra-independent-source-sha256.txt`, manifest SHA-256
  `e18c69f6c283771191f0523fdaaaa5548c96a127c5eda8b2854d3e528a2d94c6`.
- Two unrestricted-affine extension files, 221 lines:
  `logs/regular-affine-independent-source-sha256.txt`, manifest SHA-256
  `2448b9d41a935699e7b0b12ee6b304d8217544507ec423af14ddb8b0b0445f7a`.

Both manifests matched after the focused rehash build and again after the
audits. Hash-check logs are `logs/regular-algebra-independent-hash-check.log`
and `logs/regular-affine-independent-hash-check.log`. No semantic or kernel-
verification blocker was found in the reviewed scope. Public-facade
integration, package-wide consumers, archive packaging, and nonaffine
geometric theorems remain separate coordinator-owned checks.
