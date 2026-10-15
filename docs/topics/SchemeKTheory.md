# Scheme K/G-theory and sheaf geometry

Scheme K-theory is formed from actual finite locally free sheaves; coherent
G-theory uses affine-locally finite-type quasicoherent sheaves on locally
noetherian schemes. The canonical comparison is the K-map of their exact
inclusion. Geometric restriction, pullback, and finite direct image keep these
same sheaf functors and their natural comparison maps.

The derived sheaf interfaces extend this geometry to bounded-below complexes.
The actual two-chart projective line supplies cohomology, relative direct-image,
base-change, and twisted diagonal computations over every commutative ring.
Its vector bundles and explicitly bounded vector-bundle complexes have perfect
derived projection images. The triangles retain the original geometric arrows;
arbitrary locally perfect inputs and projective generation remain separate.

## Public imports

`import Quillen.AlgebraicGeometry.Scheme` exposes the selected K/G,
regular-comparison, and localization interfaces. Pullback, finite direct image,
and the sheaf geometry can be imported through their individual owners:

| Import after `Quillen.AlgebraicGeometry.` | Principal declarations |
| --- | --- |
| [`Scheme.KTheory`](../../Quillen/AlgebraicGeometry/Scheme/KTheory.lean), [`Scheme.GTheory`](../../Quillen/AlgebraicGeometry/Scheme/GTheory.lean) | `AlgebraicGeometry.Scheme.K`, `G`, `restrictK`, `restrictG` |
| [`Scheme.Comparison.KToG`](../../Quillen/AlgebraicGeometry/Scheme/Comparison/KToG.lean) | `AlgebraicGeometry.Scheme.KToG`, `KToG_restrict` |
| [`Scheme.Pullback`](../../Quillen/AlgebraicGeometry/Scheme/Pullback.lean), [`Scheme.FlatPullback`](../../Quillen/AlgebraicGeometry/Scheme/FlatPullback.lean) | `AlgebraicGeometry.Scheme.pullbackK`, `KFunctor`, `pullbackG`, `GFlatFunctor`, `KToG_pullback` |
| [`Scheme.Regular`](../../Quillen/AlgebraicGeometry/Scheme/Regular.lean) | `AlgebraicGeometry.Scheme.KToGRegularAffineEquiv`, `KToGRegularEquiv` |
| [`Scheme.Localization`](../../Quillen/AlgebraicGeometry/Scheme/Localization.lean), [`Scheme.ClosedGTheory`](../../Quillen/AlgebraicGeometry/Scheme/ClosedGTheory.lean) | `AlgebraicGeometry.Scheme.localization_longExact`, `AlgebraicGeometry.Scheme.Closed.supportedGEquiv`, `localization_longExact` |
| [`Scheme.FinitePushforward`](../../Quillen/AlgebraicGeometry/Scheme/FinitePushforward.lean), [`Scheme.FiniteFlatPushforward`](../../Quillen/AlgebraicGeometry/Scheme/FiniteFlatPushforward.lean) | `AlgebraicGeometry.Scheme.GFinitePushforwardFunctor`, `KFiniteFlatPushforwardFunctor` |
| [`Scheme.Comparison.KToGFinitePushforward`](../../Quillen/AlgebraicGeometry/Scheme/Comparison/KToGFinitePushforward.lean) | `AlgebraicGeometry.Scheme.KToGFiniteFlatPushforward` |
| [Aglib.AlgebraicGeometry.Cohomology.Functoriality.PushforwardComposition](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Cohomology/Functoriality/PushforwardComposition.lean) | `AlgebraicGeometry.Scheme.Modules.derivedPushforwardPlusCompIso` |
| [Aglib.AlgebraicGeometry.Cohomology.ProjectionFormula.Basic](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Cohomology/ProjectionFormula/Basic.lean) | `AlgebraicGeometry.Scheme.Modules.derivedProjectionFormulaIso` |
| [Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Cohomology/BaseChange/Flat.lean) | `AlgebraicGeometry.Scheme.Modules.derivedFlatBaseChangeMap` |
| [`Scheme.ProjectiveLine.DerivedCechTriangle`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/DerivedCechTriangle.lean) | `AlgebraicGeometry.Scheme.ProjectiveLine.derivedCechTriangle` |
| [`Scheme.ProjectiveLine.VectorBundleCech`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/VectorBundleCech.lean) | `AlgebraicGeometry.Scheme.ProjectiveLine.exists_original_vectorBundle_cech_model` |
| [`Scheme.ProjectiveLine.DerivedCechCone`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/DerivedCechCone.lean) | `AlgebraicGeometry.Scheme.ProjectiveLine.derivedCechConeIso` |
| [`Scheme.ProjectiveLine.DiagonalProjectedTensorTriangle`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/DiagonalProjectedTensorTriangle.lean) | `AlgebraicGeometry.Scheme.ProjectiveLine.diagonalCoefficientTensorTriangle` |
| [`Scheme.ProjectiveLine.DiagonalComplexProjectedTriangle`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/DiagonalComplexProjectedTriangle.lean) | `AlgebraicGeometry.Scheme.ProjectiveLine.diagonalDerivedComplexCoefficientTriangleFunctor` |

Unqualified declaration names continue in the preceding displayed namespace.
Below, geometric module paths abbreviated as `Scheme.…` have prefix
`Quillen.AlgebraicGeometry.`; declaration namespaces are stated independently.

## Sheaf categories, universes, and degrees

For `X : AlgebraicGeometry.Scheme.{u}`, `AlgebraicGeometry.Scheme.Modules.FiniteLocallyFree X`
is the full category of module sheaves with finite local bases. Its conflations
are actual sheaf short exact sequences, giving `vectorBundleExactStructure X`.
`AlgebraicGeometry.Scheme.K X n` is the K-group of its chosen `u + 1` small model.
This definition is available on every scheme.

`AlgebraicGeometry.Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X` tests quasicoherence and
finite type on **every** actual affine open chart. `FiniteTypeSheaves X` is
defined over every scheme, as is `AffineFiniteType R` over any affine ring.
On locally noetherian schemes the global category is abelian, with exact
structure `coherentExactStructure X`; its exact sequences are precisely the
ambient sheaf short exact sequences. The
[Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Modules/Coherent/FinitePresentation.lean), [Aglib.AlgebraicGeometry.Modules.FinitePresentation.AffineTransport](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Modules/FinitePresentation/AffineTransport.lean), [Aglib.AlgebraicGeometry.Modules.FinitePresentation.Noetherian](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Modules/FinitePresentation/Noetherian.lean)
proves that these sheaves are locally finitely presented under the same
noetherian hypothesis. Generic finite-type definitions alone do not install
these abelian or exact structures.

`AlgebraicGeometry.Scheme.K X n` and `G X n` lie in `Type (u + 1)`, whereas the separately
named `AlgebraicGeometry.Scheme.Affine.G R n` lies in `Type u` for a noetherian
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

`AlgebraicGeometry.Scheme.IsRegular X` is local noetherianity with regular local stalks.
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
`AlgebraicGeometry.Scheme.Modules.schemeKToG_bijective_of_finite_resolutions` retains its admissible
kernel-closure and actual finite-resolution premises.

## Coherent open and closed localization

For an open immersion `j : U ⟶ X`, `SupportedG j n` uses the Serre category of
coherent sheaves whose actual restriction to `U` vanishes. On a noetherian
ambient scheme, with the stated local noetherianity of `U`,
`AlgebraicGeometry.Scheme.localization_longExact j` has maps `inclusionG`, `restrictG`,
and `boundaryG`. It proves all recurring connective exactness positions and
`restrictG_zero_surjective`, including arbitrary opens of `X`.

For a closed immersion `i : Z ⟶ X` with `[IsNoetherian X]`, the
`AlgebraicGeometry.Scheme.Closed` interface constructs the actual open complement and
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

For an actual finite map `f : Z ⟶ X`, Aglib's
[finite-type quasicoherent pushforward](https://github.com/kangxyz/aglib/blob/main/Aglib/AlgebraicGeometry/Modules/QuasiCoherent/FiniteType/Pushforward.lean)
preserves affine-local finite-type quasicoherent sheaves without noetherian
assumptions. On locally noetherian source and target, the
[Quillen G-map construction](../../Quillen/AlgebraicGeometry/Scheme/Coherent/Finite/GeneralPushforward.lean)
uses the native exact functor and constructs
`AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.coherentPushforwardGMap`.
`GFinitePushforwardFunctor` has identity and composition laws; scheme-isomorphism,
open-base-change, finite-affine, and closed-immersion formulas retain the
original functors and G-maps.

Finite **flat** maps of locally noetherian schemes preserve vector bundles and
give `AlgebraicGeometry.Scheme.Modules.schemeKPushforward` and `KFiniteFlatPushforwardFunctor`.
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

`AlgebraicGeometry.Scheme.Modules.derivedPushforwardPlus f` is the installed right-derived
direct-image functor on D+. `derivedPushforwardPlusUnit f` compares actual
termwise direct image with it. The following proofs identify when that unit
is invertible, while retaining the original augmentations and units:

| Module under `Scheme.Sheaf` | Conditions and conclusion |
| --- | --- |
| [Aglib.AlgebraicGeometry.Cohomology.Affine.PushforwardAcyclicity](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Cohomology/Affine/PushforwardAcyclicity.lean), `AffineDerivedPushforward` | Every quasicoherent sheaf is acyclic for an affine morphism; the unit on its degree-zero single is invertible |
| [`AffineBoundedDerivedPushforward`](../../Quillen/AlgebraicGeometry/Scheme/Sheaf/AffineBoundedDerivedPushforward.lean) | Explicit lower and upper term bounds and degreewise quasicoherence give the same installed-unit comparison |
| [Aglib.AlgebraicGeometry.Cohomology.Flasque.Pushforward](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Cohomology/Flasque/Pushforward.lean), `FlasqueDerivedPushforward`, `FlasqueComplex`, `FlasqueComplexDerivedPushforward` | For every scheme map, flasque sheaves are acyclic and the unit is invertible on bounded-below flasque-term complexes, with no upper bound |
| [Aglib.AlgebraicGeometry.Cohomology.Godement.First](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Cohomology/Godement/First.lean) | On every scheme and all module sheaves, the actual product of stalk skyscrapers is an exact flasque-valued functor with a natural monic germ unit |
| [Aglib.AlgebraicGeometry.Cohomology.Godement.Resolution](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Cohomology/Godement/Resolution.lean) | Actual natural augmented flasque sheaf resolution from the exact cokernel iteration, with the original germ augmentation quasi-isomorphism and preservation of short exact sequences |
| [Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Basic](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Cohomology/Godement/TotalComplex/Basic.lean), `GodementTotalExact` | Actual natural totalization retains the lower bound and has flasque terms, preserving short exact sequences and degreewise monomorphisms |
| [Aglib.AlgebraicGeometry.Cohomology.Flasque.Extensions](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Cohomology/Flasque/Extensions.lean), `FlasquePushforwardExact` | Actual flasque extension closure and direct-image short-exact preservation with flasque first terms; the complex direct-image statement requires no bound |
| [Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.QuasiIso](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Cohomology/Godement/TotalComplex/QuasiIso.lean), `GodementTotalDerivedComparison` | Original total augmentation is a quasi-isomorphism for every Plus input; genuine weak maps are preserved, and Q(f_*T(K))≅Rf_*(Q(K)) is natural for every scheme map |
| [`FlatInjectivePushforward`](../../Quillen/AlgebraicGeometry/Scheme/Sheaf/FlatInjectivePushforward.lean) | Flat direct image preserves injectives; the derived-Hom adjunction retains a bounded-below injective target complex |
| [`AffineCompositeDerivedPushforward`](../../Quillen/AlgebraicGeometry/Scheme/Sheaf/AffineCompositeDerivedPushforward.lean) | The unit on `j_*M` is invertible when `j` and `j ≫ f` are affine and `M` is quasicoherent |

Affine acyclicity has no finite, flat, or noetherian assumption. For arbitrary
maps, the general flasque argument uses that direct images of injectives are
flasque. `derivedPushforwardPlusCompIso f g` constructs
`R(g ∘ f)_* ≅ Rg_* Rf_*` with the ordinary composition isomorphism and both
installed unit equations; it does not supply triple-composition coherence.

`godementFirstProduct X` is the categorical product of the original
`moduleStalk X x` and `moduleSkyscraper X x` functors. Its natural coordinate
presentation has one stalk value at each point of an open, with scalars acting
through their actual germs. Restriction discards coordinates; extension by zero
proves flasqueness, and sheaf section extensionality proves the germ unit monic,
including empty opens and schemes. Independent stalk preimages prove exactness
on every section group and module. This establishes this particular product
functor's exactness, with no quasicoherence, flatness or noetherian premise.
`GodementResolution` constructs the natural cokernel C of that germ unit,
proves it exact by the actual snake diagram, and iterates it. The resolution
has terms G(C^n M) and the original quotient/unit differential. Its augmented
sequence is exact, its terms are flasque, and its natural augmentation from
M concentrated in degree zero is a quasi-isomorphism. The resolution preserves
short exact sequences and degreewise zero objects. `GodementComplex`
totalizes the actual degreewise resolution bicomplex. An original total
degree is its finite diagonal biproduct for every lower-bounded input,
so the same lower bound and termwise flasqueness are retained.
`GodementTotalExact` proves exactness using exact coproducts in the actual
module-sheaf category. The original stalk retraction and natural quotient
sections give the signed total homotopy equivalence; exact, jointly
conservative module stalks then reflect its original augmentation
quasi-isomorphism. `godementTotalPlus` preserves genuine weak maps by
naturality and two-out-of-three. Its installed-unit comparison computes
the original derived direct image for every scheme morphism. All these
assertions allow arbitrary module sheaves and schemes, including empty
schemes, and require only the actual input lower bound. Unbounded
totalization and the perfect/flasque Waldhausen roof K model remain
separate.

The sheafified tensor bifunctor, its left unit, and finite-free retract exactness
live in [Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Basic](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/Algebra/Category/ModuleCat/Sheaf/Tensor/Basic.lean)
and `TensorExact`, with their site and universe hypotheses.
`Scheme.Sheaf.TensorRestriction` gives actual open restriction;
`Scheme.VectorBundle.TensorLocalExactness` proves short exactness for finite
locally free coefficients using affine finite-free retractions, including the
empty finite-free case. These constructions do not supply full monoidal coherence.

[Aglib.AlgebraicGeometry.Modules.Pushforward.Stalk](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Modules/Pushforward/Stalk.lean)
uses the actual pushforward germ map as a natural module-stalk isomorphism on
an inducing image and proves zero stalks off a closed image.
[Aglib.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Modules/Pushforward/ClosedImmersion.lean), [Aglib.AlgebraicGeometry.Modules.Stalk.Reflection](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Modules/Stalk/Reflection.lean)
therefore proves exact closed-immersion pushforward for arbitrary module sheaves,
without quasicoherence, finite generation or noetherian assumptions.
[Aglib.AlgebraicGeometry.Modules.Pushforward.SectionStalk](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Modules/Pushforward/SectionStalk.lean)
retains the original stalk ring retraction when the immersion is a section.

[Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Basic](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Modules/Tensor/Stalk/Basic.lean)
identifies the literal sheaf tensor stalk with the tensor of the two module
stalks, using the original pure-section germs in both directions.
[Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Naturality](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Modules/Tensor/Stalk/Naturality.lean)
preserves both original sheaf-variable maps. Neither coefficient requires
flatness or quasicoherence.

`Scheme.VectorBundle.ProjectionFormula` proves the ordinary projection formula
for every scheme map, arbitrary source module sheaf, and finite locally free
target coefficient. `projectionFormulaIso` has the original geometric
adjunction-unit composite as its forward arrow. `DerivedProjectionFormula`
gives its bounded-below derived natural isomorphism, with both-variable
naturality and the installed-unit equations; there is no upper bound or extra
global flasqueness hypothesis.

For a closed immersion and arbitrary coefficient/source module sheaves,
[Aglib.AlgebraicGeometry.Modules.ProjectionFormula.ClosedImmersion](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Modules/ProjectionFormula/ClosedImmersion.lean), [Aglib.AlgebraicGeometry.Modules.Stalk.Reflection](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Modules/Stalk/Reflection.lean)
proves the original `projectionFormulaMap` invertible, with both-variable
naturality. `PullbackStalkUnit` and `ProjectionFormulaStalk` retain its actual
adjunction-unit germ and scalar-extension tensor formula on image stalks;
both stalk objects vanish off the image. No coefficient flatness,
quasicoherence or noetherian assumption is added. This ordinary comparison
does not assert a general D+ tensor projection formula.

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

For `R : CommRingCat.{u}`, `AlgebraicGeometry.Scheme.ProjectiveLine.twoChartLine R`
glues two polynomial spectra along their Laurent overlap. `Charts`,
`AffineCechCover`, and `ChartAffineness` retain the original affine open maps
and intersection. The line is qcqs; its projection `p` is flat and separated.
`globalSectionsIso R` identifies its sections with `R` by the original base
map. `coefficientMap_isPullback` in `BaseChangeGluing` proves cartesian coefficient
change for every ring map, without flatness or noetherianity. Here all module
paths have prefix `Quillen.AlgebraicGeometry.Scheme.ProjectiveLine`, while
declarations have prefix `AlgebraicGeometry.Scheme.ProjectiveLine`.

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

### Finite-projective Čech models and the original derived image

For every quasicoherent sheaf `M` on `twoChartLine R`,
[`ModuleChartSections`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/ModuleChartSections.lean)
constructs its actual polynomial chart-section modules and their Laurent
overlap isomorphism. `chartSectionDifference_coordinates` identifies the
original first-minus-second restriction difference with the scalar-extension
unit on the positive chart minus the transported negative-chart unit. The
negative scalar map sends the polynomial coordinate to `T⁻¹`; the positive
map sends it to `T`. These coordinates and their adjunction-unit equations
are constructed from the sheaf, rather than assumed transition data.

When `M` is finite locally free, both chart modules are finite projective over
`R[X]`. They need not be free on the entire chart or finite over `R`.
[`VectorBundleCech`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/VectorBundleCech.lean)
gives a homotopy-equivalent complex of finite projective `R`-modules supported
in degrees zero and one. Its theorem
`exists_original_vectorBundle_cech_model` concerns the literal signed section
differential of the original pushed sheaf sequence. All commutative base
rings are included, with no noetherian, regular, nonzero, or reduced hypothesis.

The finite model comes from Laurent cutoff bounds, finite-free retractions
of the polynomial chart modules, and rectangular projector transition matrices.
[`LaurentProjectorFiniteDefects`](../../Quillen/Algebra/Polynomial/LaurentProjectorFiniteDefects.lean)
factors both parametrix defects through actual finite coefficient modules.
The algebraic step in
[`FiniteParametrix`](../../Quillen/Algebra/Module/FiniteParametrix.lean)
takes `d : A → B` and `s : B → A` with factorizations
`d s + t r = id_B` through `F` and `s d + u v = id_A` through `G`.
If `A` and `F` are projective and `F` and `G` finite, the enlarged split map
`[d,t] : A × F → B` has a finite-projective kernel: a genuine retraction gives
projectivity, and the proved surjection from `G × F` gives finite generation.
Its second projection to `F` supplies the replacement differential and the
original chain maps and homotopies. This proves finite generation without a
uniform coefficient-support window for the older kernel embedding in
`FiniteCoefficientRetract`; that older criterion retains its own premises.

[`CechCounit`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/CechCounit.lean)
uses the original affine counits on both pushed Čech terms and their naturality
square. `originalSheafCechSectionsIso` in
[`CechSheafComplex`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/CechSheafComplex.lean)
reconstructs the signed sheaf complex as the cone of the degree-zero
difference, shifted by `-1`. It does not assume quasicoherence of the total
ordinary direct image of `M` or commutation of sections with homology.

`derivedCechConeIso R M` identifies the actual D+ projection image, included
in the ambient derived category, with that original shifted sheaf cone.
The comparison rotates the existing derived Čech triangle, fixes its two
ordinary vertices by identity maps, and retains the connecting square and
the explicit minus-one shift. This identification needs quasicoherence,
independently of a perfectness assumption.

Combining it with the finite model proves perfection of the installed image
for every vector-bundle single. Finite induction through the actual brutal-layer
triangles extends the result to complexes with explicit lower and upper term
bounds and finite locally free terms. The strict representatives and precise
perfect-object statements are recorded in
[projective-line perfect models](PerfectComplexes.md#projective-line-strict-models).
The existence theorem does not choose coefficient-natural finite replacements
or global bounded vector-bundle representatives of arbitrary locally perfect
objects on the line.

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
vertices remain actual derived-image objects. `DiagonalGenerationEndpoints`
and `DiagonalGenerationNaturality` give the natural vector-bundle endpoint
identifications. `DiagonalLineRotation` applies the exact original line tensor
and rotation, retaining the standard negative shifted incidence; nested line
contraction and corrected derived roof representatives remain separate.

[`DiagonalRestrictedStalkExactness`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/DiagonalRestrictedStalkExactness.lean)
proves that the original incidence sequence, stalked along the diagonal and
restricted through the original projection stalk map, stays short exact after
tensor with any coefficient module. The quotient is the flat quotient-line
stalk; the coefficient module need not be flat.
[`DiagonalAllCoefficientTensor`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/DiagonalAllCoefficientTensor.lean)
transfers it through the canonical tensor/pullback stalk comparisons and
joint stalk reflection to both literal global tensor sequences. They are
short exact for every line-module coefficient and every base-module coefficient.
[`DiagonalAllCoefficientPushforward`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/DiagonalAllCoefficientPushforward.lean)
identifies the original diagonal-supported tensor term for arbitrary
coefficients through the same projection/section arrows, exactly recovering
the old bundle isomorphism.

[`DiagonalCoefficientFunctors`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/DiagonalCoefficientFunctors.lean)
realizes exactness of all three actual vertex functors. The third is the original
quotient-line tensor followed by exact diagonal pushforward through that same
ordinary natural comparison. For arbitrary bounded-below coefficient complexes,
[`DiagonalComplexTensorTriangle`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/DiagonalComplexTensorTriangle.lean)
constructs the literal degreewise short exact sequence and canonical distinguished
D+ triangle. Its whole triangle functor inverts actual quasi-isomorphisms and
descends through the original localization; the explicit inverse/forward roof
formula and connecting square preserve every derived morphism.
`DiagonalComplexProjectedTriangle` uses the original exact tensor/pushforward
units and section comparison to identify the projected third term naturally
with R(− tensor Q). `DiagonalComplexSingleComparison` proves the explicit whole
original vector-bundle single-triangle correspondence. No flatness,
quasicoherence, perfectness, noetherianity or upper term bound is imposed on the
coefficient complex. [`OriginalPerfectGeneration`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/OriginalPerfectGeneration.lean)
now identifies the original endpoints naturally on every intrinsic-perfect
D+ input, uses the specified determinant contractions and units, and gives
the signed rotated triangle p*Rp*K→K→L⊗p*(Rp*(K⊗L)[1]). Its coefficients are
perfect, its original connecting map is natural on genuine roofs, and its
full original bundle-single correspondence is explicit.

## Remaining comparisons and independent consumers

The two-chart construction has not been identified with Proj, a full
twisting-sheaf family, or the projective-bundle K-equivalence. Derived projection
perfection is proved for vector-bundle singles and explicitly bounded
vector-bundle complexes. On the actual line,
[`IntrinsicPerfectPushforward`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/IntrinsicPerfectPushforward.lean)
also constructs objectwise global strict models and proves perfection of the
original derived projection for every intrinsic perfect D+ input over an arbitrary
commutative ring. The natural intrinsic-perfect diagonal generation,
original endpoint/roof comparisons, inverse-twist contraction and signed
rotation are supplied.
[`TautologicalCoefficientPullback`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/TautologicalCoefficientPullback.lean)
identifies the actual tautological line under every coefficient change,
preserving its original inclusion and both chart trivializations without a
flatness premise. `NativeAffineTautological` specializes this to the actual
native affine comparison. Actual exact Phi and its original native two-summand
K-map correspondence are supplied on the flasque model at each fixed R.
[`FlasqueGPhiMatrix`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/FlasqueGPhiMatrix.lean)
proves the actual product-category K(G)∘K(Phi)=id, with the original four
entries and product K-equivalence, for every R and natural degree, including
zero.
[`FlasquePhiInverse`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/FlasquePhiInverse.lean)
now proves the opposite actual model K-map identity, and its original
compact-model/affine-geometry transport makes the EXISTING native affine
two-summand K-map bijective in every natural degree, including zero. The
packaged nativeAffineTwoSummandKEquiv retains that literal forward map.
P5 now supplies original native open K-map naturality and intrinsic-perfect
projection perfection over every quasi-compact base. Its exact original
flasque coefficient pair G0=p_*K and G1=p_*T_P(K RIGHT tensor L)[1] sends
acyclicity on literal p^-1 Z to acyclicity on every base open Z, without quasi-separatedness
or compact-open assumptions. The original units, total augmentation, signed
shift and supplied lower bounds are retained. Independent complex ordinary
review and native ROOT/checked-origin interfaces cover these six source
leaves. The actual native Phi model, its original K-map comparison and
inverse-image supported boundary naturality are also supplied. The EXISTING
native two-summand K-map is now bijective on every qcqs base and its original
supported map on every compact base open, for all natural degrees including
zero. Actual affine/iso/finite-cover induction and original Mayer–Vietoris
and localization ladders discharge all premises; both equivalences retain
the literal forward map and unchanged product normalization. Independent
complex ordinary reviews and native ROOT/checked-origin coverage passed.
The actual canonical positive unit and original native negative/Euler
entries now prove GΦ=id for every quasi-compact base. The independent
native Phi bijection then gives ΦG=id on qcqs bases through
[`P5NativeGlobalInverse`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/P5NativeGlobalInverse.lean),
which identifies the actual geometric G0/G1 pair with the EXISTING native
inverse in every natural degree, including zero. Independent ordinary
reviews, strict 200k sources, native style, 36 ROOT examples and complete
377-origin checked-kernel coverage passed. Arbitrary-base-map naturality
and general projective-bundle comparisons retain separate scope.
The Čech cone comparison concerns quasicoherent
singles; general bounded-below flat base change is not inferred.
The older
[`FiniteCoefficientRetract`](../../Quillen/Algebra/Module/FiniteCoefficientRetract.lean)
criterion retains its projectivity, splitting, and uniform-window premises;
the finite-defect proof above supplies a different sufficient criterion.
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
