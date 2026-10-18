# Projective-line perfect models and K-equivalences

The projective-line K-equivalence concerns the existing two-summand map on actual Waldhausen models. It includes every natural degree, including zero. The [two-chart sheaf geometry](../../Scheme/ProjectiveLine/README.md) supplies its signed Čech and diagonal inputs.

## Geometric sheaf inputs

The [two-chart sheaf geometry](../../Scheme/ProjectiveLine/README.md) supplies ordinary arrows, installed D+ units, the all-coefficient signed diagonal triangle, and natural intrinsic-perfect generation over every commutative ring, including zero. The construction retains original self-base-change/projection endpoints, connecting maps on genuine roofs, determinant contractions, units, and signed rotation. The affine and native qcqs K-inverse laws are stated below.

## Projective-line strict models

For every `R : CommRingCat.{u}` and finite locally free sheaf `M` on the actual
`twoChartLine R`, the original signed sheaf Čech complex has a strict-perfect
homotopy model on `Spec R`. The finite-projective chart-module construction
and its actual counit and signed-cone comparisons are explained in
[scheme projective-line guide](../../Scheme/ProjectiveLine/README.md).
The relevant imports have prefix
`Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine`; declaration names
in this table have prefix `Quillen.PerfectComplexes.ProjectiveLine`:

| Module | Actual perfect-complex interface |
| --- | --- |
| [`CechModel`](CechModel.lean) | `exists_strictSheafCech_model`: a strict-perfect sheaf model with both chain maps and homotopies |
| [`DerivedPushforwardVectorBundle`](DerivedPushforwardVectorBundle.lean) | `exists_derivedPushforward_vectorBundle_strict_model` and `perfect_derivedPushforward_vectorBundle`: a strict representative and intrinsic perfection of the installed D+ projection image |
| [`BoundedDerivedPushforward`](BoundedDerivedPushforward.lean) | `perfect_derivedPushforward_of_bounded_vectorBundle_terms`: perfection for explicitly bounded complexes of finite locally free terms |

The derived representative is an isomorphism in the ambient derived category
after the actual D+ inclusion, with the original projection functor unchanged.
The bounded theorem takes `K : CochainComplex.Plus (twoChartLine R).Modules`,
integer bounds `a,b`, zero terms below `a` and above `b`, and finite local
freeness of every term. Its proof uses shifts of bundle singles and finite
induction through actual brutal-layer triangles. No noetherian, regular,
free-chart, nonzero, or reduced hypothesis is imposed on the base ring.

The finite Čech construction supplies vector-bundle singles and explicitly bounded vector-bundle complexes. The intrinsic-perfect extension below additionally constructs objectwise global strict models and perfect original derived images; it does not choose coefficient-natural finite replacements. The older `FiniteCoefficientRetract` criterion still retains its uniform support-window premise.

## Two-summand maps and inverse laws

Let `P` be the original native projective line over `X`, with projection `p`
and original tautological line `L = O(-1)`. The forward functor is the existing
two-summand map, with its original product coordinates:

```text
Φ(A,B) = p^* A ⊕ (L LEFT tensor p^* B).
G(E)   = (Rp_* E, Rp_*(E RIGHT tensor L)[1]).
```

The exact original flasque model implements the actual Godement totalizations,
ordinary direct images, chosen zero objects and signed shifts. Derived
categories supply homological comparisons; the K-theory endpoints are the
actual Waldhausen models. A derived-category equivalence of the two-summand
functor is neither assumed nor generally true.
The local implementation uses direct arbitrary-ring diagonal generation;
the [projective-line route](README.md)
records its relation to TT's noetherian-reduction proof.

| Construction | Result | Source owner |
| --- | --- | --- |
| P1 | Original canonical tensor/pullback mates and determinant contractions, with both chart signs fixed | [LineTensorCompatibility](../../Scheme/ProjectiveLine/LineTensorCompatibility.lean), [PullbackTensorCompatibility](../../Scheme/ProjectiveLine/PullbackTensorCompatibility.lean) |
| P2 | Genuine QC/strict representatives and perfection of the original derived projection for every intrinsic-perfect D+ input over every commutative ring, including zero | [QuasicoherentRepresentative](QuasicoherentRepresentative.lean), [IntrinsicPerfectPushforward](IntrinsicPerfectPushforward.lean) |
| P3 | Natural diagonal generation on the actual affine two-chart line, retaining original roofs, endpoints, units and perfect coefficients | [OriginalPerfectGeneration](../../Scheme/ProjectiveLine/OriginalPerfectGeneration.lean) |
| P4 | Both original affine model K-map inverse laws and bijectivity of the unchanged native map, for all `n : ℕ`, including zero | [FlasqueGPhiMatrix](FlasqueGPhiMatrix.lean), [FlasquePhiInverse](FlasquePhiInverse.lean), [FlasqueNativePhiTransport](FlasqueNativePhiTransport.lean) |
| P5 | Both actual original qcqs model inverse laws, identification of geometric G with the unchanged native inverse, and the original compact-open supported Phi bijection | [P5NativeGlobalInverse](P5NativeGlobalInverse.lean), [NativeGlobalBundle](NativeGlobalBundle.lean), [NativeGlobalSupport](NativeGlobalSupport.lean) |

[P5PositiveUnitNative](P5PositiveUnitNative.lean)
proves that the actual canonical unit `A → p_*T(p^* A)` is weak on every
native quasi-compact base and that its literal K-map is identity.
[P5NativeGPhiLaw](P5NativeGPhiLaw.lean)
combines this unit with negative vanishing and signed Euler additivity to
prove the original `GΦ = id`, without assuming Phi bijectivity.
`P5NativeGlobalPhi` transports the already proved native qcqs Phi
bijection through the actual model inclusions. `P5NativeGlobalInverse`
then proves `ΦG = id` and identifies the actual geometric G with
`nativeGlobalTwoSummandKEquiv.symm`. The original forward map and
`Product.KEquiv` are unchanged.

Global projection perfection and the exact coefficients require a
quasi-compact base. The coefficient and Phi support-preservation statements
hold for every base open. Native global K-bijectivity additionally requires
quasi-separatedness; the supported bijection uses compact base opens. All
natural degrees include zero. Arbitrary-base-map naturality, the general
projective-bundle formula, Proj/twisting-sheaf identification, and the older
specialized P3 endpoint-unit/connecting comparisons retain separate scope.

## Proof model and geometric limitations

The K-theory framework follows TT 3.4--3.5: actual complicial/Waldhausen
complex models, with derived categories used for homological comparisons.
This selected rank-two proof is a direct arbitrary-ring diagonal-generation
route. TT 4.3--4.4 instead first reduces the projective-bundle theorem to
noetherian schemes and develops the regular-sheaf Quillen argument; see the
[original proof, printed pp. 329--330](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Thomason-Trobaugh.pdf#page=83).
The local proof implementation therefore differs, while the target remains the
original two-summand map. The [bounded-flat comparison guide](../BoundedFlat/BassComparison.md) records the chosen Lean model's raw-track/cube comparisons.

Start on the actual P¹ over an arbitrary commutative ring R, including the
zero ring. The target is the existing `nativeTwoSummandKMap`, in every
nonnegative degree including zero, induced by

```text
Φ(A,B) = p* A ⊕ (O(-1) ⊗ p* B).
G(E)   = (Rp* E, Rp*(E ⊗ O(-1))[1]).
```

The actual K-inverse G is realized on the original exact flasque model. Φ is not
generally an equivalence of perfect derived categories: cross-Hom between its two
summands need not vanish. Generation therefore feeds a K-additivity proof,
not ordinary equivalence/approximation of this two-summand functor.

Two concrete restrictions govern this route. `Scheme.Regular.ResolutionProperty`
assumes local noetherianity and cannot supply P2 unchanged. Global direct
chain representatives also fail: for nonzero R, H¹(P¹_R,O(-2))≅R, whereas
literal chain maps O[0]→O(-2)[1] vanish. The Čech quotient is
R[T,T⁻¹]/(R[T]+T⁻²R[T⁻¹]), detected by the T⁻¹ coefficient; see
[Stacks 01XT](https://stacks.math.columbia.edu/tag/01XT). P4 needs genuine
roofs, with source replacement when necessary. Object strictification alone
does not prove the K-model comparison.

## Intrinsic-perfect representatives

The intrinsic-perfect strictification uses a termwise quasi-coherent, bounded-below
representative with local strict models in a finite interval [a,b]. For a<b,
finite generators of the actual top homology on both affine charts lift to
cycle sections. The chart denominator and graph-gluing construction extends
them through powers of the actual line and supplies a finite vector-bundle
map V[-b]→K epimorphic on Hᵇ. Its actual cone has strict chart amplitude
[a,b−1]. At a=b the genuine terminal cycles are finite locally free; finite
reassembly identifies a strict global derived model. These actual cone and
quasi-isomorphism verifications are accepted without noetherian assumptions.
It uses bounded affine counits, their original derived-unit maps, the literal
lifted signed two-chart Čech arrow and its rotated triangle to construct a
bounded termwise-QC model of the original input. The intrinsic consumer obtains
its actual global strict model and perfect Rp image.  These objectwise derived isomorphisms do not supply P4's
exact/natural roof model.

Relevant source
anchors are [Stacks 0F8E](https://stacks.math.columbia.edu/tag/0F8E),
[0F8F](https://stacks.math.columbia.edu/tag/0F8F) and
[0GMM](https://stacks.math.columbia.edu/tag/0GMM); use finite-type
quasicoherence rather than coherence over a possibly noncoherent R.

## Flasque K-model and geometric inverse

The accepted `Scheme/Sheaf/GodementFirst` constructs the actual first Godement
functor on all scheme module sheaves: the product of stalk skyscrapers, with
its natural monic germ unit, flasque values and exactness. Its explicit sections
are pointwise stalk products, and their exactness is proved directly rather
than inferred from arbitrary sheaf products. `GodementResolution` now constructs
the exact natural cokernel functor, its iterates, the augmented flasque sheaf
resolution and the original germ augmentation quasi-isomorphism. The resolution
functor preserves short exact sequences. The accepted ten-source total family
now supplies the actual natural totalization on all lower-bounded complexes
of arbitrary module sheaves on every scheme. `GodementComplex` retains the
same lower bound and has flasque terms; `GodementTotalExact` preserves
short exact sequences and degreewise monomorphisms. The original signed
stalk contraction and joint homology reflection prove the actual total
augmentation quasi-isomorphism in `GodementTotalQuasiIso`, whose naturality
also proves preservation of genuine weak arrows.
`GodementTotalDerivedComparison` constructs the natural installed-unit
comparison Q(f_*T(K))≅Rf_*(Q(K)) for every scheme map and every Plus input.

`FlasqueBoundedBelow` now constructs the actual full Waldhausen model of
lower-bounded locally perfect complexes with flasque terms, its literal
inclusion and exact Godement total functor, and both forward natural weak
units. `FlasqueBoundedBelowComparison` proves the two original K-map inverse
laws in every nonnegative degree, including zero, on every scheme; its literal
comparison to all perfect complexes requires quasi-compactness.
`FlasquePushforwardExact` proves actual sheaf and complex short-exact
preservation with flasque first terms, without bounds. These source results supply the exact model and a pushforward foundation;
`FlasqueCoefficientZero`, `FlasqueCoefficientOperations` and
`FlasqueCoefficientOne` now supply the actual exact G₀=p_* and
G₁=p_*T(−⊗L)[1], with flasque-perfect values, original maps, lower bounds and
native shift signs. Their product is exact, and their natural comparisons
retain the installed derived units, actual augmentation and inclusion-shift
equations.  `FlasqueTwoSummands` and `FlasqueTwoSummandComparison` now supply
actual exact Phi=T_P(p*A coproduct (L tensor p*B)) and its original forward
weak unit/categorical coproduct comparison. `TautologicalCoefficientPullback`
preserves the original line inclusion and both chart trivializations under
arbitrary coefficient change. `NativeAffineTautological` and
`NativeAffineTwoSummands` compare the actual original native geometry, twist
and two-summand functor.
[`FlasqueNativePhiKMap`](FlasqueNativePhiKMap.lean)
retains the EXISTING original native two-summand K-map after literal model
inclusion and actual inverse affine pullback, with unchanged Product.KEquiv
and chosen-zero rebasing, for every R and every natural degree including zero.
Naturality is in coefficient-complex maps at each fixed R.
[`StrictPositiveRetraction`](StrictPositiveRetraction.lean)
now proves the canonical geometric unit followed by pushed actual total
augmentation is a genuine quasi-isomorphism on the original strict affine
coefficients. Its actual forward weak span proves the original positive
K-map equality. `StrictPositiveSourceComparison` proves the literal strictTotal
source K-map bijective in every natural degree, including zero, using the
original affine strict inclusion and proved lower-bounded/flasque comparisons.
There is no natural strictification premise.
[`FlasqueShift`](../FlasqueShift.lean)
now proves inversion for the actual signed model shift K-map on every scheme
and in every natural degree, including zero, through the original identity
cone, genuine cofibration/cofiber structure and weak-zero natural map.
`EulerSequence`, `EulerFunctors`, `EulerNegative`, `EulerAdditivity` and
`EulerMiddle` retain the original determinant-normalized Euler sequence after
coefficient tensor, actual totalization and ordinary projection. Its real
conflation gives K(E1)=K(E2)*K(E0), and its literal weak-zero middle gives
K(E1)=1.
[`EulerInverse`](EulerInverse.lean)
then proves K(E2[1])=K(E0) on every original strict affine source;
`EulerConnecting` separately preserves the original connecting isomorphism
and native shift sign. Outputs remain locally perfect/flasque, rather than
termwise strict.
[`FlasqueGPhiMatrix`](FlasqueGPhiMatrix.lean)
now proves both the actual original product-category K(G)∘K(Phi)=id and
the literal composite KMap(Phi⋙G)=id. Its four entries retain the actual
positive units, negative vanishing, Euler comparison and signed shift; proved
strictTotal K-map surjectivity and the unchanged Product.KEquiv extend them
to every flasque coefficient input.
over every R, including the zero ring, and every natural degree, including
zero. The opposite PhiG identity and its actual natural endpoint weak-span
comparisons are now supplied below. The native qcqs/support extension is supplied below.
[`FlasqueTensorDiagonalAdditivity`](FlasqueTensorDiagonalAdditivity.lean)
now gives K(Gamma E2)=K(Gamma E1)*K(Gamma E3) from the literal original
diagonal conflation after exact LEFT-L tensor and totalization.
[`FlasquePhiColumns`](FlasquePhiColumns.lean)
expresses actual K(Phi)(K(G)(x)) as the positive composite times the inverse
unshifted negative composite, using the original sum functor, product
coordinates and actual base shift.
[`FlasquePhiInverse`](FlasquePhiInverse.lean)
now combines the actual first negative-column, second positive-column and
third identity K-map comparisons with that original additivity and native
K-group commutativity. It proves K(Phi)∘K(G)=id and literal KMap(G⋙Phi)=id
in every natural degree, including zero. Together with GPhi it makes the
SAME original Phi K-map bijective.
[`FlasqueNativePhiTransport`](FlasqueNativePhiTransport.lean)
retains the original compact-model inclusions, unchanged product
K-equivalence and actual affine inverse pullback to prove bijectivity of
the EXISTING nativeTwoSummandKMap. The packaged nativeAffineTwoSummandKEquiv
has that literal forward map.  for the final ten-source family; All rings include zero and all natural degrees
include zero. This closes affine P4. The separate specialized P3
endpoint-unit/connecting comparisons, Proj/twisting-sheaf
identification, Bass cube and final TT identification are not conclusions
of this argument. No unbounded Godement augmentation is asserted.

`NativeOpenNaturality` proves
the original native two-summand K-map square for actual base open immersions
in every natural degree, including zero. `NativeProjectionPerfect` proves
perfectness of the original derived projection for every intrinsic-perfect
D+ input on the native projective line over any quasi-compact base, and
local perfectness of literal ordinary p_*K on the original flasque model.
`P5NativeCoefficientsZero` and `P5NativeCoefficientsOne` give exact literal
G0=p_*K and G1=p_*T_P(K RIGHT tensor L)[1], preserving an original lower
bound a and the shifted bound a-1 respectively. `P5NativeCoefficientsSupport`
proves both coefficients preserve acyclicity on the literal inverse image
of every base open, without quasi-separatedness or compactness of that open.
The original derived unit, total augmentation, shift comparisons and their
naturality are retained. `P5NativePhi`, `P5NativePhiObjects`, `P5NativePhiComparison` and
`P5NativePhiSupport` now construct the actual native Phi model with the
original LEFT line tensor, chosen coproduct and total augmentation. Its
K-map after model inclusion is the EXISTING nativeTwoSummandKMap, with the
unchanged Product.KEquiv. Model support and the original unbounded-perfect
two-summand functor preserve acyclicity on literal p^-1 Z for every base
open Z. `NativeBoundaryNaturality` and `NativeInverseImageBoundary` give
the actual supported functor, original forget-support square and original
localization-boundary naturality for qcqs bases and compact opens, including
K1(open) to supported K0. No caller-supplied open isomorphism is needed.
`NativeGlobalBundle` now proves bijectivity of the original native map for
every qcqs base and every natural degree, including zero. Its actual affine
and scheme-isomorphism cases feed a proved compact binary-union step using
the original T-first Mayer–Vietoris restriction, difference and connecting
maps. `NativeFiniteCoverInduction` first handles finite affine unions on
separated schemes, then compact overlaps inside each newly added affine
chart on a general qcqs scheme. The original final local-pair K0 exactness
supplies the required fifth-term slice without overlap-K0 surjectivity.
`NativeGlobalSupport` then discharges all ambient bijectivity premises in
the original supported localization ladder for every compact base open.
Both packaged equivalences have the literal existing forward map and
original product coordinates.
These results close global and supported Phi bijectivity.

The four `P5PositiveUnit` sources now prove that the actual canonical
unit A→p_*T(p^*A) is a natural weak map on every quasi-compact native base,
without a termwise-QC, QS or supplied projection-isomorphism premise.
`P5NativeNegativeVanishing`, `P5NativeOffDiagonal` and the native Euler
sources retain the actual right tensor, original totalization and signed
shift; their matrix is the pair of identical positive coefficients.
[`P5NativeGPhiLaw`](P5NativeGPhiLaw.lean)
therefore proves GΦ=id in both original product coordinates and the actual
product-model KMap, on every quasi-compact base and every natural degree.
It does not use Phi bijectivity.
[`P5NativeGlobalPhi`](P5NativeGlobalPhi.lean)
transports the already proved native qcqs bijection through the literal
model inclusions.
[`P5NativeGlobalInverse`](P5NativeGlobalInverse.lean)
then proves ΦG=id on qcqs bases and identifies the transported actual
G0/G1 pair with the EXISTING nativeGlobalTwoSummandKEquiv.symm. No inverse
is used to define geometric G. This closes P5 at the stated native qcqs
and supported-Phi scope.
Final TT identification remains open.

## Positive Bass row and remaining Laurent boundary

The original positive exact row is now proved for
`K_m(S) := PerfectK(Spec S, m)`, every commutative R including zero, and
every n ≥ 0:

```text
1 → K_(n+1)(R) → K_(n+1)(R[T])²
  → K_(n+1)(R[T,T^-1]) → K_n(R) → 1.
```

[`BassPositiveCharts`](BassPositiveCharts.lean),
[`BassPositiveMayerVietoris`](BassPositiveMayerVietoris.lean)
and [`BassPositiveFundamental`](BassPositiveFundamental.lean)
retain the actual polynomial evaluation retraction, positive restriction
times inverse negative restriction, and first O-coordinate of the same
native Phi inverse after the original T-first Mayer–Vietoris boundary.
The connecting coefficient image is exactly `(a,a⁻¹)`. , including K1 to K0.

[`ScalarForwardRelativeBoundary`](../ScalarForwardRelativeBoundary.lean)
now computes the original coarse forward scalar K1 class under the actual
relative localization boundary as the actual acyclic cofiber K0 class.
The original inverse-prefix normalization and double-loop transpose give
two inversions, which cancel. The original fine Laurent [T] terminal boundary, its lower negative-chart
inversion and actual O/O(-1) zero-locus class remain open. They are still
needed for a natural Laurent splitting; exactness and the relative sign
alone do not supply it. Classical ring-K identification, Nil vanishing,
homotopy invariance and negative stabilization are not conclusions of these
rows. Keep all Nil contributions in the chart images/quotient.

## Declaration locators

These additional names use the same objects, hypotheses, and original maps as the linked construction sections. They are locators within those interfaces, not stronger comparison statements.

| Declaration / module | Construction and conditions |
| --- | --- |
| `PushforwardModuleStalk`, `ClosedPushforwardExactness`, `SectionPushforwardModuleStalk`, `TensorStalkIso`, `TensorStalkNaturality`, `ScalarExtensionTensor`, `SectionPullbackStalk`, `SectionPullbackTensorStalk`, `SheafStalkShortExact`, `ClosedImmersionProjectionFormula` | [Two-summand maps and inverse laws](#two-summand-maps-and-inverse-laws) |
| `AlgebraicGeometry.PerfectComplexes.ProjectiveLine.DerivedPushforwardVectorBundle`, `Quillen.PerfectComplexes.ProjectiveLine.perfect_derivedPushforward_vectorBundle` | [Two-summand maps and inverse laws](#two-summand-maps-and-inverse-laws) |
| `AlgebraicGeometry.PerfectComplexes.ProjectiveLine.BoundedDerivedPushforward`, `Quillen.PerfectComplexes.ProjectiveLine.perfect_derivedPushforward_of_bounded_vectorBundle_terms` | [Two-summand maps and inverse laws](#two-summand-maps-and-inverse-laws) |
| `AlgebraicGeometry.PerfectComplexes.ProjectiveLine.QuasicoherentRepresentative`, `Quillen.PerfectComplexes.ProjectiveLine.exists_quasicoherent_model_of_perfect_plus` | [Two-summand maps and inverse laws](#two-summand-maps-and-inverse-laws) |
| `AlgebraicGeometry.PerfectComplexes.ProjectiveLine.IntrinsicPerfectPushforward`, `Quillen.PerfectComplexes.ProjectiveLine.exists_strict_model_of_perfect_plus`, `perfect_derivedProjection_of_perfect` | [Two-summand maps and inverse laws](#two-summand-maps-and-inverse-laws) |
