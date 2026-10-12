# Scheme K/G-theory and sheaf geometry

Scheme K-theory is formed from actual finite locally free sheaves; coherent
G-theory uses affine-locally finite-type quasicoherent sheaves on locally
noetherian schemes. The canonical comparison is the K-map of their exact
inclusion. Geometric restriction, pullback, and finite direct image keep these
same sheaf functors and their natural comparison maps.

The derived sheaf interfaces extend this geometry to bounded-below complexes.
The actual two-chart projective line supplies cohomology, relative direct-image,
base-change, and twisted diagonal computations over every commutative ring.
Their derived triangles retain the original geometric arrows; the remaining
perfectness and projective-bundle comparisons are stated separately.

## Public imports

`import Quillen.AlgebraicGeometry.Scheme` exposes the selected K/G,
regular-comparison, and localization interfaces. Pullback, finite direct image,
and the sheaf geometry can be imported through their individual owners:

| Import after `Quillen.AlgebraicGeometry.` | Principal declarations |
| --- | --- |
| [`Scheme.KTheory`](../../Quillen/AlgebraicGeometry/Scheme/KTheory.lean), [`Scheme.GTheory`](../../Quillen/AlgebraicGeometry/Scheme/GTheory.lean) | `Quillen.Scheme.K`, `G`, `restrictK`, `restrictG` |
| [`Scheme.Comparison.KToG`](../../Quillen/AlgebraicGeometry/Scheme/Comparison/KToG.lean) | `Quillen.Scheme.KToG`, `KToG_restrict` |
| [`Scheme.Pullback`](../../Quillen/AlgebraicGeometry/Scheme/Pullback.lean), [`Scheme.FlatPullback`](../../Quillen/AlgebraicGeometry/Scheme/FlatPullback.lean) | `Quillen.Scheme.pullbackK`, `KFunctor`, `pullbackG`, `GFlatFunctor`, `KToG_pullback` |
| [`Scheme.Regular`](../../Quillen/AlgebraicGeometry/Scheme/Regular.lean) | `Quillen.Scheme.KToGRegularAffineEquiv`, `KToGRegularEquiv` |
| [`Scheme.Localization`](../../Quillen/AlgebraicGeometry/Scheme/Localization.lean), [`Scheme.ClosedGTheory`](../../Quillen/AlgebraicGeometry/Scheme/ClosedGTheory.lean) | `Quillen.Scheme.localization_longExact`, `Quillen.Scheme.Closed.supportedGEquiv`, `localization_longExact` |
| [`Scheme.FinitePushforward`](../../Quillen/AlgebraicGeometry/Scheme/FinitePushforward.lean), [`Scheme.FiniteFlatPushforward`](../../Quillen/AlgebraicGeometry/Scheme/FiniteFlatPushforward.lean) | `Quillen.Scheme.GFinitePushforwardFunctor`, `KFiniteFlatPushforwardFunctor` |
| [`Scheme.Comparison.KToGFinitePushforward`](../../Quillen/AlgebraicGeometry/Scheme/Comparison/KToGFinitePushforward.lean) | `Quillen.Scheme.KToGFiniteFlatPushforward` |
| [`Scheme.Sheaf.DerivedPushforwardComposition`](../../Quillen/AlgebraicGeometry/Scheme/Sheaf/DerivedPushforwardComposition.lean) | `Quillen.SchemeSheaf.derivedPushforwardPlusCompIso` |
| [`Scheme.VectorBundle.DerivedProjectionFormula`](../../Quillen/AlgebraicGeometry/Scheme/VectorBundle/DerivedProjectionFormula.lean) | `Quillen.SchemeSheaf.derivedProjectionFormulaIso` |
| [`Scheme.Sheaf.DerivedFlatBaseChange`](../../Quillen/AlgebraicGeometry/Scheme/Sheaf/DerivedFlatBaseChange.lean) | `Quillen.SchemeSheaf.derivedFlatBaseChangeMap` |
| [`Scheme.ProjectiveLine.DerivedCechTriangle`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/DerivedCechTriangle.lean) | `Quillen.Scheme.ProjectiveLine.derivedCechTriangle` |
| [`Scheme.ProjectiveLine.DiagonalProjectedTensorTriangle`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/DiagonalProjectedTensorTriangle.lean) | `Quillen.Scheme.ProjectiveLine.diagonalCoefficientTensorTriangle` |

Unqualified declaration names continue in the preceding displayed namespace.
Below, geometric module paths abbreviated as `Scheme.…` have prefix
`Quillen.AlgebraicGeometry.`; declaration namespaces are stated independently.

## Sheaf categories, universes, and degrees

For `X : AlgebraicGeometry.Scheme.{u}`, `Quillen.SchemeSheaf.FiniteLocallyFree X`
is the full category of module sheaves with finite local bases. Its conflations
are actual sheaf short exact sequences, giving `vectorBundleExactStructure X`.
`Quillen.Scheme.K X n` is the K-group of its chosen `u + 1` small model.
This definition is available on every scheme.

`Quillen.CoherentScheme.affineLocallyFiniteType X` tests quasicoherence and
finite type on **every** actual affine open chart. `FiniteTypeSheaves X` is
defined over every scheme, as is `AffineFiniteType R` over any affine ring.
On locally noetherian schemes the global category is abelian, with exact
structure `coherentExactStructure X`; its exact sequences are precisely the
ambient sheaf short exact sequences. The
[`finite-presentation comparison`](../../Quillen/AlgebraicGeometry/Scheme/Coherent/FinitePresentation.lean)
proves that these sheaves are locally finitely presented under the same
noetherian hypothesis. Generic finite-type definitions alone do not install
these abelian or exact structures.

`Quillen.Scheme.K X n` and `G X n` lie in `Type (u + 1)`, whereas the separately
named `Quillen.Scheme.Affine.G R n` lies in `Type u` for a noetherian
`R : CommRingCat.{u}`. `Affine.moduleEquiv` identifies the latter with finite-module
G-theory through actual affine global sections. These presentations retain
their universe bounds; the global group is not definitionally replaced by
the lower-universe affine group.

K and G have index `n : ℕ` and use exact-category `K_n = π_(n+1)(BQ)`.
In the sheaf sections below, `D+` means `DerivedCategory.Plus X.Modules`,
using cochain complexes indexed by `ℤ` with a lower bound. A sheaf is placed
in degree zero by `singleZeroPlus` or the corresponding derived single functor;
`rightDerived n` denotes the `n`th derived image for `n : ℕ`.

## Restriction, pullback, and the canonical comparison

`restrictK j n` and `restrictG j n` are the canonical small-K maps of actual
open restriction. G-restriction requires local noetherianity of source and
target. `KToG X n` is the original small-K map of
`vectorBundleToCoherentExact X`; `KToG_restrict` preserves the square of
these original restrictions.

`pullbackK f n` accepts every scheme map. Pullback preserves finite local
freeness, and the local splitting of vector-bundle short exact sequences gives
exactness without flatness. Its identity and composition laws define
`KFunctor n` on the opposite of the full scheme category; on open immersions,
`pullbackK_eq_restrictK` identifies the old restriction map.

`pullbackG f n` instead requires `[Flat f]` and locally noetherian source and
target. Exact flat sheaf pullback gives `coherentExactPullback f`, with its
identity, composition, and open-restriction laws. `GFlatFunctor` is defined on
the opposite category of locally noetherian schemes with flat morphisms;
`KToGFlatNatTrans` retains the original K-to-G maps. The theorem
`KToG_pullback` expresses that naturality on each flat map.

The vector-bundle/strict-perfect K comparison holds on every scheme, and
strict-perfect K also has all-map pullback. Pullback on localized perfect K
has its separate quasi-compactness boundary. Those models and their comparisons
are described in [perfect-complex K-theory](PerfectComplexes.md).

## Regular K-to-G comparison

For `[IsRegularRing R]`, `KToG_regular_affine_bijective R n` and
`KToGRegularAffineEquiv R n` cover every nonnegative degree on `Spec R`, with
the original `KToG` as forward map. The proof constructs actual finite
vector-bundle resolutions from objectwise finite projective dimension.
There is no finite Krull-dimension restriction or common resolution bound.
PID and dimension-at-most-one specializations remain in `Scheme.Regular`.

`Quillen.Scheme.IsRegular X` is local noetherianity with regular local stalks.
For a nonaffine scheme, `KToGRegularEquiv X n` requires this regularity,
`[CompactSpace X]` (quasi-compactness), and `[HasResolutionProperty X]`.
The resolution property says that every coherent sheaf is an actual quotient
of a finite locally free sheaf. It supplies coherent syzygies; the regular,
quasi-compact argument produces the finite resolutions needed by
[Quillen resolution](Localization.md#resolving-subcategories-and-actual-finite-resolutions).
Regularity alone does not supply the resolution property.

`KToGRegularEquiv_coe` retains the canonical comparison, and
`KToGRegularEquiv_spec` identifies its affine specialization with the
independently constructed regular-affine equivalence. The more general
`SchemeSheaf.schemeKToG_bijective_of_finite_resolutions` retains its admissible
kernel-closure and actual finite-resolution premises.

## Coherent open and closed localization

For an open immersion `j : U ⟶ X`, `SupportedG j n` uses the Serre category of
coherent sheaves whose actual restriction to `U` vanishes. On a noetherian
ambient scheme, with the stated local noetherianity of `U`,
`Quillen.Scheme.localization_longExact j` has maps `inclusionG`, `restrictG`,
and `boundaryG`. It proves all recurring connective exactness positions and
`restrictG_zero_surjective`, including arbitrary opens of `X`.

For a closed immersion `i : Z ⟶ X` with `[IsNoetherian X]`, the
`Quillen.Scheme.Closed` interface constructs the actual open complement and
derives noetherianity of `Z`. `supportedGEquiv i n` identifies G of that
original closed scheme with the supported term by dévissage. Its composite
with supported inclusion is exactly `pushforwardG i n`, the actual coherent
sheaf direct image. The transported `boundaryG i n` gives

```text
… → G_(n+1)(U) → G_n(Z) → G_n(X) → G_n(U) → … → G_0(U) → 0.
```

Principal closed/open and arbitrary-ideal affine specializations preserve the
same geometric maps; the complement of an arbitrary ideal need not be affine.
The [localization guide](Localization.md) explains the Serre theorem and its
finite-module applications underlying these geometric sequences.

## Finite direct image

For an actual finite map `f : Z ⟶ X`,
[`Scheme.Coherent.Finite.GeneralPushforward`](../../Quillen/AlgebraicGeometry/Scheme/Coherent/Finite/GeneralPushforward.lean)
proves preservation of affine-local finite-type quasicoherent sheaves without
noetherian assumptions. On locally noetherian source and target, it proves
exactness and constructs `CoherentScheme.Finite.coherentPushforwardGMap`.
`GFinitePushforwardFunctor` has identity and composition laws; scheme-isomorphism,
open-base-change, finite-affine, and closed-immersion formulas retain the
original functors and G-maps.

Finite **flat** maps of locally noetherian schemes preserve vector bundles and
give `SchemeSheaf.schemeKPushforward` and `KFiniteFlatPushforwardFunctor`.
Target noetherianity is used to make the affine finite flat modules finite
projective; exactness is transported through coherent inclusion.
`KToGFiniteFlatPushforward` is the natural transformation with the original
K-to-G components. These hypotheses do not give vector-bundle direct image
for every finite map or over arbitrary nonnoetherian bases.

[`PerfectComplexes.FiniteFlatPushforward`](../../Quillen/AlgebraicGeometry/PerfectComplexes/FiniteFlatPushforward.lean)
uses the same sheaf direct image on strict-perfect complexes, proves
quasi-isomorphism preservation using exact coherent direct image, and defines
`Quillen.PerfectComplexes.strictKFiniteFlatPushforward`.
`FiniteFlatPushforwardNaturality` preserves `vectorBundleToStrictKMap` in every
nonnegative degree. `DerivedPushforwardComparison` identifies strict direct
image with installed D+ direct image. The theorem
[`Affine.perfectDerivedObjects_derivedPushforwardPlus`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/DerivedFiniteFlatPushforward.lean)
preserves intrinsic D+ perfectness for affine source and a finite flat map to
a locally noetherian target; general-source preservation is separate.

## Derived direct image, tensor, and projection formulas

`Quillen.SchemeSheaf.derivedPushforwardPlus f` is the installed right-derived
direct-image functor on D+. `derivedPushforwardPlusUnit f` compares actual
termwise direct image with it. The following proofs identify when that unit
is invertible, while retaining the original augmentations and units:

| Module under `Scheme.Sheaf` | Conditions and conclusion |
| --- | --- |
| [`AffinePushforwardAcyclicity`](../../Quillen/AlgebraicGeometry/Scheme/Sheaf/AffinePushforwardAcyclicity.lean), `AffineDerivedPushforward` | Every quasicoherent sheaf is acyclic for an affine morphism; the unit on its degree-zero single is invertible |
| [`AffineBoundedDerivedPushforward`](../../Quillen/AlgebraicGeometry/Scheme/Sheaf/AffineBoundedDerivedPushforward.lean) | Explicit lower and upper term bounds and degreewise quasicoherence give the same installed-unit comparison |
| [`FlasquePushforwardAcyclicity`](../../Quillen/AlgebraicGeometry/Scheme/Sheaf/FlasquePushforwardAcyclicity.lean), `FlasqueDerivedPushforward`, `FlasqueComplex`, `FlasqueComplexDerivedPushforward` | For every scheme map, flasque sheaves are acyclic and the unit is invertible on bounded-below flasque-term complexes, with no upper bound |
| [`FlatInjectivePushforward`](../../Quillen/AlgebraicGeometry/Scheme/Sheaf/FlatInjectivePushforward.lean) | Flat direct image preserves injectives; the derived-Hom adjunction retains a bounded-below injective target complex |
| [`AffineCompositeDerivedPushforward`](../../Quillen/AlgebraicGeometry/Scheme/Sheaf/AffineCompositeDerivedPushforward.lean) | The unit on `j_*M` is invertible when `j` and `j ≫ f` are affine and `M` is quasicoherent |

Affine acyclicity has no finite, flat, or noetherian assumption. For arbitrary
maps, the general flasque argument uses that direct images of injectives are
flasque. `derivedPushforwardPlusCompIso f g` constructs
`R(g ∘ f)_* ≅ Rg_* Rf_*` with the ordinary composition isomorphism and both
installed unit equations; it does not supply triple-composition coherence.

The sheafified tensor bifunctor, its left unit, and finite-free retract exactness
live in [`Quillen.Algebra.Category.ModuleCat.Sheaf.Tensor`](../../Quillen/Algebra/Category/ModuleCat/Sheaf/Tensor.lean)
and `TensorExact`, with their site and universe hypotheses.
`Scheme.Sheaf.TensorRestriction` gives actual open restriction;
`Scheme.VectorBundle.TensorLocalExactness` proves short exactness for finite
locally free coefficients using affine finite-free retractions, including the
empty finite-free case. These constructions do not supply full monoidal coherence.

`Scheme.VectorBundle.ProjectionFormula` proves the ordinary projection formula
for every scheme map, arbitrary source module sheaf, and finite locally free
target coefficient. `projectionFormulaIso` has the original geometric
adjunction-unit composite as its forward arrow. `DerivedProjectionFormula`
gives its bounded-below derived natural isomorphism, with both-variable
naturality and the installed-unit equations; there is no upper bound or extra
global flasqueness hypothesis.

## Canonical base-change mates

On a genuine cartesian square, `Scheme.Sheaf.CartesianBaseChange` constructs
the geometric mate from pullback/direct-image adjunctions.
`AffineScalarAdjunction`, `AffineScalarSquare`, and `AffineBaseChange` identify
it with the extension/restriction-of-scalars mate on spectra. It is invertible
on every quasicoherent sheaf in an affine cartesian square, without flatness
or finite-generation assumptions, retaining the original tensor and unit formulas.
`CartesianBaseChangePasting`, `CartesianBaseChangeHorizontal`, and
`CartesianBaseChangeLocalization` give vertical/horizontal equations and
open-cover detection with their local invertibility premises explicit.

`derivedFlatBaseChangeMap` is constructed from that same ordinary mate, with
a flat base leg and an actual cartesian square. Flatness of the pulled-back
leg follows from the square; exact pullback preserves homology without an
injective-preservation assumption. Its defining equation keeps both installed
composite units. The scope of invertibility is:

| Module under `Scheme.Sheaf` | Invertibility proved |
| --- | --- |
| [`DerivedOpenBaseChange`](../../Quillen/AlgebraicGeometry/Scheme/Sheaf/DerivedOpenBaseChange.lean), `CartesianOpenBaseChangeMate`, `DerivedFlatBaseChangeOpen` | Every bounded-below complex for an open base leg and arbitrary scheme map; the installed open comparison is the same canonical mate |
| [`AffineDerivedBaseChange`](../../Quillen/AlgebraicGeometry/Scheme/Sheaf/AffineDerivedBaseChange.lean), `AffineDerivedBaseChangeCoordinates`, `AffineDerivedBaseChangeLocal` | Quasicoherent singles and their integer shifts for affine morphisms and flat base change, including nonaffine ambient schemes |

`DerivedFlatBaseChangeShift`, `DerivedFlatBaseChangeHorizontal`,
`DerivedFlatBaseChangeVertical`, and `DerivedFlatBaseChangeLocalization` retain
shift, pasting, and target-open equations. `DerivedOpenCoverConservativity` and
`DerivedFlatBaseChangeOpenCover` give cover conservativity.
`AffineCompositeDerivedBaseChange` and `TwoOpenDerivedBaseChange` transport the
mate through actual chart images and the signed two-open triangle. General
bounded-below flat-base-change invertibility is not inferred from the single-sheaf
results.

## The actual two-chart line

For `R : CommRingCat.{u}`, `Quillen.Scheme.ProjectiveLine.twoChartLine R`
glues two polynomial spectra along their Laurent overlap. `Charts`,
`AffineCechCover`, and `ChartAffineness` retain the original affine open maps
and intersection. The line is qcqs; its projection `p` is flat and separated.
`globalSectionsIso R` identifies its sections with `R` by the original base
map. `coefficientMap_isPullback` in `BaseChangeGluing` proves cartesian coefficient
change for every ring map, without flatness or noetherianity. Here all module
paths have prefix `Quillen.AlgebraicGeometry.Scheme.ProjectiveLine`, while
declarations have prefix `Quillen.Scheme.ProjectiveLine`.

`Tautological` constructs a line subbundle `L` of the structure-module square
with columns `(1,t)` and `(s,1)` and Laurent transition `T`, inverse `T⁻¹`.
`TautologicalQuotient` constructs its actual line cokernel `Q`, chart rows
`(-t,1)` and `(-1,s)`, inverse transition, and the original short exact sequence.
The additive exact `TwistMinusFunctor` is a kernel negative-twist functor on
all module sheaves and preserves finite local freeness. `TwistMinusUnit`
identifies its structure-module value with `L`, retaining the inclusion;
`VectorBundleTwistMinus` gives exact twisted bundle pullback and `twistedPullbackKMap`.
Its identification with tensor by `L` remains a separate comparison.

### Signed Čech cohomology

`Scheme.Sheaf.TwoOpenSheafSequence` proves the signed Čech short exact sheaf
sequence for every sheaf on a genuine two-open cover, with the original
restriction-adjunction units, local splittings, and arrow naturality. It has
no quasicoherence, flasqueness, affine, or noetherian premise.
`TwoOpenCohomology` gives the section-complex sequence for flasque-term
complexes and actual injective resolutions; `AffineOpenCohomology` and
`SectionsHomologyZero` retain the restricted resolution and its augmentation.
`twoAffineRightDerivedOneIsoCokernel` in `TwoOpenFirstCohomology` identifies
first derived sections of a quasicoherent sheaf on a two-affine cover with
the cokernel of the literal signed restriction difference, retaining the
quotient square without requiring an affine overlap. `TwoAffineCohomology`
adds higher vanishing when the overlap is affine.

Applying these results to the original charts gives:

| Sheaf on the two-chart line | Actual derived sections |
| --- | --- |
| Any quasicoherent sheaf | Vanishing in degrees `n + 2`, by `isZero_rightDerived_globalSections_add_two` |
| Structure module | Sections `R` and no positive cohomology; `structureSheaf_difference_coordinates` retains the signed Laurent calculation |
| Negative tautological line `L` | Zero in every degree, including sections, by `TautologicalSections` and `TautologicalCohomology` |
| Tautological quotient `Q` | Sections `R × R` through the original quotient projection and no positive cohomology, by `TautologicalQuotientCohomology` |

These statements include nonreduced and zero rings; arbitrary quasicoherent
sheaves are not asserted to have vanishing first cohomology.

### Relative direct image and base change

`StructureSheafDirectImage`, `TautologicalDirectImage`, and `DerivedDirectImage`
compute direct image under `p`: the structure module has canonical image the
base structure module and no positive derived images, while `L` has zero
derived image in every degree. The D+ comparisons retain the geometric
projection unit, the given injective resolution, and principal-open section
complexes. `VectorBundleDirectImage` proves the unit invertible on pullbacks
of affine-base vector bundles and their derived negative twists zero.
`VectorBundleComplexDirectImage` extends this to complexes with explicit lower
and upper term bounds and finite locally free terms, retaining the degreewise
geometric unit. The proofs do not assume sections commute with sheaf homology.

`derivedCechTriangle R M` computes `Rp_*M` for every quasicoherent single as
the first vertex of a distinguished triangle; the other vertices are ordinary
direct images of the chart pair and overlap. Its differential is the
pushforward of the signed sheaf restriction difference, and its connecting
arrow is the original short-exact connecting map through the installed
overlap-unit inverse. Actual affine chart and overlap units discharge acyclicity.
`ProjectiveLine.DerivedFlatBaseChange` proves the canonical mate invertible on
every such single for flat cartesian base change of `p`. Its self-base-change
isomorphism uses the actual relative square and projections; its hom is the
original mate followed by the installed flat-pullback single comparison.

## The twisted diagonal triangle

On the relative square, `DiagonalIncidence` constructs
`p₁*L → p₂*Q → Δ_*Q`. The four original affine-rectangle scalars are
`t-u`, `tv-1`, `1-su`, and `v-s`. `DiagonalMonomorphism`,
`DiagonalClosedImmersion`, and `DiagonalCokernel` prove incidence monic,
the relative diagonal closed, and the original quotient the actual cokernel.
The resulting sequence is short exact over every commutative ring, using the
genuine rectangle cover, principal kernels, and cartesian adjunction mates.

`DiagonalTensorTriangle` treats affine-base bundle coefficients;
`DiagonalBundleTensorTriangle` tensors by `p₁*E` for every projective-line
vector bundle `E`, using actual tensor restriction and local exactness. The
distinguished triangles retain incidence, quotient, connecting arrows, and
coefficient naturality. `DiagonalTensorPushforward` identifies the ordinary
diagonal-supported term by the original projection arrow.
`DiagonalDerivedTensorTriangle` identifies the third vertex with installed
`RΔ_*(E ⊗ Q)`. `DiagonalProjectedTensorTriangle` then applies derived second
projection; canonical composition and the geometric section identity identify
the third vertex with the degree-zero single of `E ⊗ Q`. The first two
vertices remain actual derived-image objects.

## Remaining comparisons and independent consumers

The two-chart construction has not been identified with Proj, a full
twisting-sheaf family, or projective-bundle generation. Its Čech and flat
base-change results concern quasicoherent singles; coefficient perfection and
general bounded-below base change are not inferred. The finite-coefficient
retract criterion in
[`Quillen.Algebra.Module.FiniteCoefficientRetract`](../../Quillen/Algebra/Module/FiniteCoefficientRetract.lean)
retains projectivity, splitting, and uniform finite-window premises; no
production application discharges a missing perfect-pushforward conclusion.
Proper pushforward, general-source derived perfect preservation, and
unrestricted unbounded derived direct image remain separate.

Existing independent clients illustrate these precise interfaces:
[Scheme](../../examples/downstream/Consumer/Scheme.lean) checks geometric
restrictions and K-to-G naturality;
[Regular](../../examples/downstream/Consumer/Regular.lean) checks regular
affine/nonaffine comparisons and forward maps;
[ClosedGTheory](../../examples/downstream/Consumer/ClosedGTheory.lean) and
[AffineClosed](../../examples/downstream/Consumer/AffineClosed.lean) retain
actual closed/open maps;
[FinitePushforward](../../examples/downstream/Consumer/FinitePushforward.lean),
[FiniteFlatPushforward](../../examples/downstream/Consumer/FiniteFlatPushforward.lean),
and [StrictFiniteFlatPushforward](../../examples/downstream/Consumer/StrictFiniteFlatPushforward.lean)
use direct-image comparison laws;
[AffineDerivedPushforward](../../examples/downstream/Consumer/AffineDerivedPushforward.lean)
and [DerivedPushforwardComparison](../../examples/downstream/Consumer/DerivedPushforwardComparison.lean)
use the original installed units to detect equality of derived arrows.
These clients do not add the remaining geometric comparisons.
