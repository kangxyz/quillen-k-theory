# Mathematical scope

The library develops algebraic K-theory through several constructions and
comparisons. Its Q/S K-theory models are connective; separate Bass negative groups are
defined by functorial cokernel recursion. Lean declarations specify the actual
objects, maps, hypotheses, and parameter ranges. This guide records principal
interfaces and remaining boundaries.

## Available families

| Family | Current scope |
| --- | --- |
| Exact categories and Q-construction | Exact structures, restricted spans, composition, compatible functors, and canonical K-maps |
| Dévissage and resolution | Abelian finite-filtration dévissage and admissible finite-resolution comparisons |
| Serre and G-localization | Specified Serre quotients, finite-module G-theory, and connective tails |
| Scheme K/G-theory | Vector bundles, finite-type/coherent sheaves, restriction, K→G, and noetherian open/closed localization |
| Regular K→G | Regular affines; quasi-compact regular schemes with the resolution property |
| Perfect complexes | Strict/local models, derived local perfectness, change of cofibrations, support, and bounded-flat representatives |
| Model comparisons | Gillet–Waldhausen with explicit term hypotheses; vector-bundle/strict equivalence on every scheme; affine strict/local equivalence |
| Global perfect localization | Quasi-compact open immersions into qcqs schemes; positive equivalence, exact K₀ image, boundary, and connective tail |
| Supported localization and naturality | Quasi-compact auxiliary acyclicity opens on qcqs bases; arbitrary commuting support/localization squares |
| Support excision | Open image and auxiliary open cover the base; original supported K-equivalence in all nonnegative degrees, without compactness/separation |
| Mayer–Vietoris | Quasi-compact two-open covers of qcqs schemes, including matching K₀-class gluing; supported version with a quasi-compact auxiliary open |
| Pullback | Vector-bundle/strict K for all scheme maps; perfect K and localized perfect spectra between quasi-compact schemes; flat coherent G pullback |
| Waldhausen fibration/cofinality | Explicit closure/cylinder hypotheses, canonical spectrum fiber comparison, positive equivalences, and degree-zero tails |
| Spectra and stable fibers | Iterated S Ω-spectrum, additive K-comparison, signed parameter-loop shift, and all-integer stable fiber sequence |
| Stable localization | Coherent-homotopy quotient, categorical localization at all-integer stable equivalences, descended groups, and exact-functor laws |
| Bass groups | Actual affine, scheme, and supported cokernel recursions seeded by homotopical perfect K₀; natural affine/scheme comparison |
| Affine Bass step and projective line | Laurent-unit transition; two-chart projective line, qcqs structure, flat projection, and global sections |

[Library.md](Library.md) gives import paths and qualified interfaces.
Generic finite-type sheaf categories exist over arbitrary rings/schemes; their
abelian, Serre, exact-category, and G-theory results retain the stated noetherian
or locally noetherian hypotheses.

## Localization, excision, and degree zero

For `j : U ⟶ X`, `PerfectOpenK j n` uses locally perfect objects on `X` with
weak equivalences detected on `U`. The relative sequence has the actual
support-forgetting map and homotopy-fiber boundary. Its surjective degree-zero
map lands in this relative group.

For quasi-compact quasi-separated (qcqs) `X` and quasi-compact `U`, relative
restriction is an equivalence in positive degrees. In degree zero it is
injective with image exactly `(perfectKRestrict j 0).range`. The tail

```text
K₁(X) → K₁(U) → K₀(X on X ∖ U) → K₀(X) → K₀(U)
```

is exact at the three interior positions. Surjectivity onto final `K₀(U)` is
not asserted. Principal affine opens are included over every commutative ring,
including localization at zero.

Ordinary localization is natural for commuting qcqs open-pair squares with
quasi-compact opens. With auxiliary support, the relative boundary needs only
quasi-compact ambient bases; relative restriction additionally needs
quasi-compact localization opens. The actual boundary and positive inverse are
natural for arbitrary commuting support/localization squares when the bases
are qcqs and both localization and auxiliary opens are quasi-compact. Flatness
and cartesianness are not required. Fixed-base support inclusions and forgetting
support are included.

The supported relative bounded-flat comparison includes K₀, requiring only
quasi-compactness of `X`, with arbitrary opens and no quasi-separatedness.
Support excision includes all nonnegative degrees when the localization image
and auxiliary open cover `X`, with an actual extension-by-zero inverse and no
compactness/separation hypothesis.

A quasi-compact two-open cover of a qcqs scheme has the connective
Mayer–Vietoris sequence and matching local K₀-class gluing. The overlap map is
the first restriction multiplied by the inverse of the second. The supported
version requires a quasi-compact auxiliary acyclicity open. Neither overlap K₀
surjectivity nor a negative boundary is supplied by these connective results.
See [ThomasonTrobaugh.md](ThomasonTrobaugh.md).

## Spectra and Bass groups

The iterated S-spectrum uses its original cylinder loop transitions.
`originalKStableEquiv` preserves the group law in every nonnegative degree,
including K₀. Its negative stable groups vanish. Arbitrary exact functors have
named stable-map laws and original K-map naturality without a chosen-zero
image equality. Their normalized prespectrum maps have identity/composition
homotopies; after stable localization these become literal equalities.

Parameter looping transposes loop/structure coordinates and has the signed
all-integer stable shift. It is distinct from the older looping and square-cone
constructions. Actual path-space fibers have an all-integer stable long exact
sequence for arbitrary prespectra; fibers of Ω-spectra retain the Ω condition.
Whole coherent based-square homotopies supply fiber maps and boundary
naturality. Vanishing of all integer fiber groups detects stable equivalence.
Connectivity of a fiber of connective inputs uses degree-zero surjectivity.
The structural Waldhausen comparison supplies that premise in its stated
fibration setting.

Categorical stable localization has descended stable-group functors and a
universal property. Perfect spectra form a contravariant functor there for
arbitrary maps between quasi-compact schemes, using the inverse of the
bounded-flat inclusion and retaining original K-maps and flat pullback.
The bounded-flat localized functor accepts all schemes.

Bass negative groups are actual cokernel recursions seeded by homotopical
perfect or supported K₀ in additive form. Index `n` means degree `-n`.
Scheme pullback accepts arbitrary maps between quasi-compact schemes;
supported pairs require only a quasi-compact ambient base and allow arbitrary
vanishing opens. The affine ring and scheme-product recursions agree naturally
in all nonpositive degrees, with literal K₀ in degree zero.

The affine Laurent unit, inverse, scalar action, whole spectrum homotopy, and
one-step `affineBassTransition` are constructed. The two-chart projective line
has its actual Laurent gluing, qcqs structure, flat projection, and global
sections `R`. These results do not identify the cokernel groups with negative
Bass spectral groups or algebraic Grothendieck K₀. The finite-coefficient
retract criterion remains conditional on its projectivity/splitting and uniform
finite-window assumptions, without a production pushforward application.

## Remaining comparisons

- Coherently functorial spectral Bass iteration and comparison with the cokernel groups.
- The fundamental theorem, projective-bundle formula, and Laurent-boundary calculation.
- Negative Thomason–Trobaugh localization, negative boundaries, and nonconnective descent.
- Stable mapping-cone/cofiber exactness, quotient homotopy invariance, and telescope stable-group comparisons.
- A standard stable model structure or triangulation for the constructed categorical localization.
- Proj identification, twisting sheaves, higher projective-line cohomology, and perfect pushforward.
- Strict/local equivalence on arbitrary nonaffine schemes and perfect pullback on arbitrary non-quasi-compact schemes.
- The Waldhausen algebraic Grothendieck presentation versus homotopical K₀; general exact-category dévissage/localization and full Serre-pair coherence.
- Cross-universe transport beyond the explicit small-model comparisons, plus-construction comparisons, and higher raw-spectrum associativity coherence.

Regularity alone does not give the resolution property. Finite cube HELP does
not imply arbitrary compact HELP, and endpoint collar deformation alone does
not supply vertical lifting. Keep these hypotheses when composing interfaces.

## Verification

The candidate's complete compile, lint, and audits are pending. A scoped,
matched typechecking measurement is recorded in [Performance.md](Performance.md).
The configured check is `bash scripts/check.sh --rehash`: generation,
layout and placeholder checks, script tests, library/tests, Batteries environment
lint, native mathlib text lint, downstream clients, and explicit audit replay.
Allowed foundation axioms are `propext`, `Classical.choice`, and `Quot.sound`.
See [Architecture.md](Architecture.md#trust-checks) for declaration coverage and
[CONTRIBUTING.md](../CONTRIBUTING.md#typechecking-performance) for profiling.

Successful checks concern encoded statements and audited foundation
dependencies in the checked environment. Mathematical interpretation and
applicability require their own assessment; passing checks does not supply an
absent comparison theorem.
