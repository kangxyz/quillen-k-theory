# Independent review: global regular-scheme canonical K-to-G

Reviewed 2026-10-09. Lean 4.34.0, pinned mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

## Verdict and exact scope

**Accepted:** for an actual scheme `X`, ordinary regularity, quasi-compactness,
and the ordinary resolution property prove bijectivity of the original
`Quillen.Scheme.KToG X n` for every `n : ℕ`. The equivalence
`Quillen.Scheme.KToGRegularEquiv X n` has that exact homomorphism as its
forward map, definitionally. No mathematical or kernel-assumption blocker
was found in the eight-module scope below.

The accepted hypotheses are exactly:

- `Quillen.Scheme.IsRegular X`: local noetherianity and regularity of every
  actual structure-sheaf stalk.
- `CompactSpace X`: quasi-compactness, without a Hausdorff condition. With
  local noetherianity this is the ordinary noetherian-scheme condition.
- `Quillen.Scheme.HasResolutionProperty X`: every coherent sheaf admits an
  epimorphism from an actual finite locally free sheaf.

This does not assume finite Krull dimension, a sheaf-independent resolution
bound, global projectivity of vector bundles, a finite resolution, a
homotopy equivalence, or a K-equivalence. It does not prove the resolution
property from regularity alone. It concerns connective, nonnegative
vector-bundle K-groups and coherent G-groups in their existing upper-universe
small models, not negative K-theory or a replacement by perfect-complex
K-theory.

## Semantic inspection

### Ordinary hypotheses and genuine categories

`Regularity.lean` defines regularity on actual stalk rings and proves its
affine-chart characterization by the actual open-immersion stalk maps and
`Spec.stalkIso`. The mathlib `IsRegularLocalRing` used here means a
noetherian local ring whose maximal ideal has generator rank equal to its
Krull dimension; it contains no homological or K-theoretic hypothesis.
`isRegular_spec_iff` identifies the scheme condition with `IsRegularRing`.
These formulations agree with [Stacks 02IR, Lemmas 28.9.2–3](https://stacks.math.columbia.edu/tag/02IR).

`HasResolutionProperty` has only an existence field for a vector-bundle
object and an epimorphism to each coherent object. Its equivalence
`hasResolutionProperty_iff_sheaf_epi` explicitly proves the epimorphism is
an epimorphism of the underlying module sheaves. On a noetherian scheme this
is the usual resolution property, as described in [Stacks 0F85, Definition
36.36.1 and the following paragraph](https://stacks.math.columbia.edu/tag/0F85).
The affine instance is independently constructed from a finite free module
cover and the actual coherent/finite-module equivalence; it needs only a
noetherian ring, not regularity.

The foundational definitions were inspected as dependencies:
`CoherentScheme.coherent` checks finite quasicoherence on every actual affine
chart; `IsFiniteLocallyFree` records finite local bases; and
`coherentExactStructure` and `vectorBundleExactStructure` use all ambient
sheaf short exact sequences. They do not redefine coherent sheaves as
objects with finite vector-bundle resolutions, or vector bundles as globally
projective objects. The coherent inclusion preserves and reflects the
relevant exactness and epimorphisms.

### Locality and kernel closure

`VectorBundle/Locality.lean` transports finite local bases along genuine
isomorphisms and the open-subscheme/over-site equivalence. It composes the
cover data using `QuasicoherentData.bind` and verifies both finite generating
sets and the basis isomorphisms. For a cover indexed in a larger universe,
it chooses an open image containing each point of `X`, obtaining a small
cover before composing the local bases. Joint surjectivity is used, not
assumed descent of the conclusion.

`KernelClosure.lean` restricts an actual coherent short exact sequence to
each affine chart. Its two vector-bundle terms become finite projective
modules there, so the established affine kernel-closure instance applies.
Locality then proves the original coherent kernel finite locally free.
This is local projectivity and local splitting only; there is no lift or
splitting in the global coherent or sheaf category.

### Objectwise bound and actual finite resolutions

`AffineChartDimension.lean` defines its chart functor as actual coherent
restriction, followed by the genuine affine coherent/finite-module
equivalence and the inclusion into all modules. It proves preservation of
short exact sequences and identifies chart-module projectivity with finite
local freeness on that chart. Consequently a global vector-bundle quotient
has a projective middle module on every chart, and the projective dimension
of its coherent kernel drops by one whenever the quotient has positive
bounded projective dimension.

`ChartBounds.lean` applies the independently reviewed
`projectiveDimension_ne_top_of_regular` to those finite chart modules. This
previous theorem globalizes local regular-ring bounds by open free loci of
actual finite syzygies, so it does not assume finite-dimensional affine
rings. A finite affine subcover of `X` supplies only a finite maximum of
bounds for the particular sheaf being resolved. It does not take a maximum
over all sheaves or assert a finite bound on the scheme's Krull dimension.

`GlobalResolution.lean` inducts on this maximum. In the successor case the
ordinary resolution property supplies an actual bundle epimorphism, and
`exists_vectorBundle_shortExact` uses its genuine categorical coherent
kernel. The induction decreases every chart bound simultaneously. At zero,
chart-module projectivity and locality show that the final coherent syzygy
is already a vector bundle.

The result is the actual `ExactStructure.FiniteResolution` datatype:
`of_mem` records a terminal resolving object, while `step` retains a short
complex, its conflation proof, a resolving middle term, and a resolution of
the kernel. Thus all maps, syzygies, ambient exact sequences, and the
original target are retained. The separate length-bounded theorem is an
intermediate construction; its chart bound is discharged in the final
regular/quasi-compact endpoint.

### The original canonical comparison

`GlobalComparison.lean` applies the existing
`schemeKToG_bijective_of_finite_resolutions` to the newly proved actual
resolutions and kernel closure. Its other closure conditions were proved
for genuine vector bundles. The adapter transports the finite conflation
towers to the chosen small coherent category, retaining their targets
through the equivalence's isomorphisms.

The vector-bundle small-model lift is an actual exact equivalence with the
inherited full subcategory, not just a categorical equivalence with an
unchecked exact structure. `vectorBundleSmall_factor` identifies its
composite with the original inclusion. The already proved full Quillen
resolution theorem then applies, and `ExactFunctor.KMap_comp` identifies
its forward map with the original scheme comparison. The latter was
rechecked directly in `Scheme/Comparison/KToG.lean`: it is precisely the
small-model K-map of the actual bundle-to-coherent exact inclusion.

`KToGRegularEquiv_toMonoidHom` and the elementwise forward-map consumer both
check by `rfl`. Open-restriction naturality is inherited from the existing
geometric square. Its stated equivalence theorem assumes regularity,
quasi-compactness, and the resolution property for both source and target;
this review does not infer a new resolution-property inheritance theorem.
`KToGRegularEquiv_spec` proves equality with the independently constructed
regular-affine equivalence, not merely existence of another isomorphism.

## Dependency scope

The accepted unrestricted-affine algebra and general geometric adapter are
reviewed in `docs/REVIEW_20261009_REGULAR_AFFINE_K_G.md`; the full objectwise-
finite Quillen theorem is reviewed in
`docs/REVIEW_20261009_FULL_RESOLUTION.md`; the original affine vector-bundle
and small-model adapters are reviewed in
`docs/REVIEW_20261009_CANONICAL_PID_K_G.md`.

All ten current regular-algebra/affine hashes and all fourteen full-resolution
hashes still match their reviewed manifests. The older PID manifest contains
a now-removed compatibility wrapper and the old import path in
`AffineResolution.lean`. This is exactly the canonical-import update already
recorded in the PID review: reversing only that import replacement recovers
the historical SHA-256 of `AffineResolution.lean` byte for byte. All other
PID-manifest sources match. The reconciliation is logged in
`logs/global-regular-independent-20261009/canonical-pid-compatibility.log`;
there is no hidden proof-body change in that adapter.

## Verification and reproducibility

The recovered prior independent build,
`logs/global-regular-independent-build.log`, explicitly rebuilt all eight
reviewed modules and passed with 3,485 jobs. The eight frozen source hashes
and the recovered independent audit hash were verified before new checks.

The fresh current-source command was:

```
ELAN_HOME=/workspace/shared/elan
PATH="$ELAN_HOME/bin:$PATH"
lake --rehash build Quillen.Scheme.Regular.GlobalComparison
lake env lean audits/GlobalRegularResolutionIndependentAudit.lean
```

It was serialized under `/tmp/quillen-lean-slot-1.lock`. The rehash build
passed with 3,485 jobs, reusing validated unchanged outputs. The independent
Lean audit passed with exit code zero. Logs are
`logs/global-regular-independent-20261009/build.log` and
`logs/global-regular-independent-20261009/all-axioms.log`.

The audit selects declarations by their exact defining module, including
private and generated declarations, and uses `Lean.collectAxioms` on every
selected declaration to traverse its recursive axiom dependencies. It
rejects every axiom except `propext`, `Classical.choice`, and `Quot.sound`.
All **83 declarations in eight modules** passed:

- VectorBundle.Locality: 12
- Regular.KernelClosure: 1
- Regular.Regularity: 13
- Regular.ResolutionProperty: 11
- Regular.AffineChartDimension: 13
- Regular.ChartBounds: 4
- Regular.GlobalResolution: 3
- Regular.GlobalComparison: 26

Its arbitrary-universe consumer examples compile for the ordinary
hypotheses, actual finite resolutions, chart-bounded resolution construction,
the ordinary ambient-sheaf epi formulation, the all-affine regularity
criterion, the affine resolution-property instance, the canonical
forward-map identities by `rfl`, and agreement with the affine equivalence.
The printed final theorem type exposes only the three advertised hypotheses.
The open-restriction theorem type is also recorded in the audit output.

All eight source files were additionally elaborated directly in manifest
order with `lake env lean -j1 SOURCE`, serialized under the same slot lock.
Every direct check passed; these checks actually elaborate the current
source rather than only reusing its build output. Log:
`logs/global-regular-independent-20261009/direct-sources.log`.

The source-token audit passes without proof placeholders or custom
assumptions. Relevant logs are in
`logs/global-regular-independent-20261009/`, including `precheck.log`,
`dependencies-hash-check.log`, `source-token-audit.log`, and
`final-hash-check.log`. The eight source hashes, audit hash, ten regular-
algebra/affine dependency hashes, and fourteen full-resolution hashes were
checked again after all direct source elaborations and still match.

Frozen source scope: eight modules, 752 lines,
`logs/global-regular-20261009/sources.sha256`. Manifest SHA-256:

`b81f9540d535dd0f94533a8d2f15149ae5604e65a841823acfd3cc50c98da87c`

Recovered independent audit SHA-256:

`2d9d7fc9bbb185487f9697a51c9c1e3a813c0b0001743fd8c225b432b50836ed`

No library proof source was modified by this review. Public-facade
integration, package-wide builds, archive packaging, and perfect-complex
comparison endpoints remain separate coordinator-owned checks.
