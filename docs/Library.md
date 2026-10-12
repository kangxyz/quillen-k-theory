# Library guide

Use an individual module for one interface. Whole-topic facades are convenient
for broader developments; `import Quillen` imports the complete library.
[Scope.md](Scope.md) records principal hypotheses and open boundaries, and
[ThomasonTrobaugh.md](ThomasonTrobaugh.md) gives the geometric localization and
Bass comparison route. [PlusConstruction.md](PlusConstruction.md) gives the ring
plus/Q comparison and scalar-extension route. Lean declarations specify the
actual maps and conditions.

## Migration to 0.4.1

Version 0.4.1 moves reusable sheaf and complex constructions to their generic
owners. Update precise imports and the qualified names listed below. The old
paths and names have no compatibility aliases or forwarding facades. The
existing coherent, vector-bundle, and perfect-complex consumers import the lower
owners for their own proofs. This is a local development version.

In the following tables, geometric module paths have prefix
`Quillen.AlgebraicGeometry`.

| Previous owner | Current owner | Declarations |
| --- | --- | --- |
| `Scheme.Coherent.Affine.Exact` | `Scheme.Sheaf.TildeExact` | `tilde_map_app_injective`, `tilde_preservesMonomorphisms`, `tilde_preservesHomology`, `tilde_preservesFiniteLimits` move from `Quillen.CoherentScheme` to `Quillen.SchemeSheaf` |
| `Scheme.VectorBundle.Pullback` | `Scheme.Sheaf.PullbackFree` | `Quillen.SchemeSheaf.pullbackUnitIso`, `pullbackFreeIso`, `pullbackRestrictIso` keep their names |
| `Scheme.Coherent.ClosedImmersion.GeneralPushforward` | `Scheme.Sheaf.PushforwardIso` | `Quillen.CoherentScheme.ClosedImmersion.General.pushforwardIsoRestrict` becomes `Quillen.SchemeSheaf.pushforwardIsoRestrict` |
| `Scheme.Coherent.ClosedImmersion.GeneralPushforward` | `Scheme.Coherent.AffineDetection` | `Quillen.CoherentScheme.ClosedImmersion.General.coherent_isZero_of_affineRestrictions` becomes `Quillen.CoherentScheme.coherent_isZero_of_affineRestrictions` |
| `Scheme.Coherent.ClosedImmersion.AffinePushforward` | `Scheme.Sheaf.AffinePushforward` | `pushforwardGlobalSectionsIso`, `isQuasicoherent_pushforward`, `tildePushforwardIso` move from `Quillen.CoherentScheme.ClosedImmersion` to `Quillen.SchemeSheaf` |
| `Scheme.Coherent.ClosedImmersion.AffinePullback` | `Scheme.Sheaf.AffinePullback` | `tildePullbackIso`, `isQuasicoherent_pullback` make the same namespace move |
| `Scheme.Coherent.Localization.AffineSectionsBaseChange` | `Scheme.Sheaf.OpenBaseChange` | Declaration names are unchanged |
| `Scheme.Coherent.Localization.GluingSubobjects` | `Scheme.Sheaf.GluingSubobjects` | Declaration names are unchanged |
| `Scheme.Coherent.Localization.LocalIsomorphisms` | `Scheme.Sheaf.LocalIsomorphisms` | Declaration names are unchanged |
| `PerfectComplexes.OpenInjectiveModel` | `Scheme.Sheaf.ComplexPushforward` | `Quillen.PerfectComplexes.pushforwardComplex` keeps its name and remains available through the former consumer |
| `Scheme.Sheaf.AffineOpenCohomology` | `Scheme.Sheaf.RestrictionSections` | The two restriction-section isomorphisms keep their names |
| `Scheme.Sheaf.CartesianOpenBaseChange` | `Scheme.Sheaf.CartesianBaseChange` | `Quillen.SchemeSheaf.cartesianPushforwardSquare` keeps its name and remains available transitively |

The generic acyclic-resolution and D+ single-complex comparisons are owned by
`Scheme.Sheaf.AcyclicPushforwardResolution` and
`Scheme.Sheaf.AcyclicDerivedPushforward`. The affine interfaces specialize those
proofs. `singleZeroPlus` retains its name in the latter owner. The genuine
`affineFiniteSheaf_pullback` stays in
`Scheme.Coherent.ClosedImmersion.AffinePullback`, importing its generic and
coherent dependencies explicitly. The object-level coherent inclusion is in
`Scheme.VectorBundle.Coherent`; its names remain available through
`Scheme.Comparison.KToG`.

The three modules
`Quillen.Waldhausen.GilletWaldhausen.StupidTruncation{Maps,Transition,Layer}`
move to `Quillen.Algebra.Homology.StupidTruncation.{Maps,Transition,Layer}`.
Their declaration names and proofs are preserved. Generic split-monomorphism
helpers belong to `Quillen.Algebra.Homology.DegreewiseSplitMono`.

The generic realized-arrow and groupoid-completion owners move from
`Quillen.KTheory.FundamentalGroup.Basic` and `Completion` to
`Quillen.Topology.ClassifyingSpace.ArrowPaths` and
`Quillen.Topology.ClassifyingSpace.GroupoidCompletion`.
Their namespaces, declaration names, statements, and proof bodies are preserved;
update precise imports. There are no legacy facades at the old paths.

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.CategoryTheory.ExactCategory.Basic` | Exact structures and conflations |
| `Quillen.CategoryTheory.QConstruction.Basic` | Quillen's Q-construction |
| `Quillen.KTheory.API` | Exact-category K-groups, canonical maps, equivalences, and small models |
| `Quillen.KTheory.GrothendieckComparison.Equivalence` | Classical exact-category K₀ comparison |
| `Quillen.Waldhausen.Basic` | Cofibrations, weak equivalences, and chosen zero |
| `Quillen.Waldhausen.KTheory` | Connective S-construction groups |
| `Quillen.Waldhausen.GrothendieckComparison.SmallModel` | Classical Waldhausen K₀ with independent object and morphism universes |
| `Quillen.Waldhausen.Approximation.Basic` | Generic approximation property |
| `Quillen.Waldhausen.FunctorialFactorization.Basic` | Generic functorial cofibration factorization |
| `Quillen.Devissage.Homotopical` | Finite-filtration dévissage |
| `Quillen.Resolution` | Admissible finite-resolution comparisons |
| `Quillen.Localization.Serre.LocalizationTheorem` | Connective Serre localization |
| `Quillen.GTheory.FiniteModules.LocalizationSequence` | Finite-module G-localization |
| `Quillen.Topology.DeformationRetract.Basic` | Cylinder deformation retracts and pushout transport |
| `Quillen.Topology.MappingCylinder.Basic` | Interval maps, cylinder projections, and retracts |
| `Quillen.Topology.HELP.Basic` | Homotopy extension and continuous cylinder coordinates |
| `Quillen.Topology.Pushout.HomotopyEquivalence` | Homotopy gluing and specified component maps |
| `Quillen.Topology.Realization.SubfamilyHEP` | Homotopy extension for realized simplicial subfamilies |
| `Quillen.AlgebraicGeometry.Scheme` | Selected geometric K/G interfaces |
| `Quillen.AlgebraicGeometry.PerfectComplexes.GlobalLocalization` | Perfect localization for quasi-compact opens of qcqs schemes |
| `Quillen.AlgebraicGeometry.PerfectComplexes.MayerVietoris` | Connective two-open sequence and matching K₀-class gluing |
| `Quillen.AlgebraicGeometry.PerfectComplexes.BassNegativeGroups` | Scheme Bass groups from perfect K₀ |
| `Quillen.Waldhausen.SConstruction.Iterated.StableFunctoriality` | Iterated S-spectrum, additive K-comparison, and exact-functor laws |
| `Quillen.Topology.Prespectrum.StableLocalization` | Coherent-homotopy quotient and categorical stable localization |

Whole-topic imports include `Quillen.Algebra`, `Quillen.CategoryTheory`,
`Quillen.Topology`, `Quillen.KTheory`, `Quillen.Devissage`, `Quillen.Resolution`,
`Quillen.Localization`, `Quillen.GTheory`, `Quillen.AlgebraicGeometry`, and
`Quillen.Waldhausen`. `Quillen.AlgebraicGeometry.PerfectComplexes` is a generated
nested facade; individual modules have smaller dependency closures.

## Module paths and namespaces

Geometric source lies under `Quillen.AlgebraicGeometry.Scheme` and
`Quillen.AlgebraicGeometry.PerfectComplexes`; principal declaration namespaces
are `Quillen.Scheme`, `Quillen.SchemeSheaf`, and `Quillen.PerfectComplexes`.
Paths describe mathematical ownership and need not match declaration namespaces.
For example, import `Quillen.AlgebraicGeometry.Scheme.Pullback` and
`Quillen.AlgebraicGeometry.PerfectComplexes.Basic` for those canonical interfaces.
Topological foundations lie under `Quillen.Topology`, while categorical
Theorem B interfaces remain under `Quillen.CategoryTheory.TheoremB`.
Approximation and functorial factorization have generic interfaces separate
from `Quillen.Waldhausen.SplitComplexes`.

| Construction | Declaration namespace |
| --- | --- |
| Cylinder deformation retracts | `Quillen.CylinderStrongDeformationRetract` |
| Primitive mapping-cylinder maps | `Quillen.MappingCylinder` |
| Homotopy extension and general cancellation | `Quillen` |
| Pushout homotopies and gluing | `Quillen.Pushout` |
| Realization coproducts and subfamilies | `Quillen.Realization` |
| Cylinder boundary data | `Quillen.CylinderBoundary` |
| Compact mapping-cylinder lifting | `Quillen.MappingCylinder.Compact` |
| Source and target mapping-cylinder collars | `Quillen.MappingCylinder.SourceCollar`, `Quillen.MappingCylinder.TargetCollar` |
| Fiberwise bridge projection, charts, and collars | `Quillen.FiberwiseBridge`, `Quillen.FiberwiseBridge.SourceCharts`, `Quillen.FiberwiseBridge.TargetCollar` |
| Sequential and skeletal Cartesian realization | `Quillen.CartesianRealization.Sequential`, `Quillen.CartesianRealization.Skeletal` |

The cylinder, retraction, and homotopy-extension owners have generic topology
dependencies; Theorem A and B consume their public interfaces. Composition and
coercion lemmas follow their canonical simplification direction. Equivalence
coercions use `_coe`; normalize underlying homomorphisms with
`MulEquiv.toMonoidHom_eq_coe` before rewriting.

## Exact categories and canonical maps

For an exact structure `E`, `E.QCategory` is its restricted-span category,
`E.KSpace` its classifying space, `E.kBasepoint` its chosen point, and `E.K n`
its connective K-group. `E.SmallK n` is the chosen small-model interface.
An exact functor `F : ExactFunctor E E'` induces `F.mapQ`, `F.KMap n`, and
`F.smallKMap n`, with identity, composition, and natural-isomorphism laws.
For composable `G`, the pointwise law is

```lean
(F.comp G).KMap n x = G.KMap n (F.KMap n x)
```

`SmallExactCategory.ofExactStructure E` bundles the input;
`SmallExactCategory.KFunctor n` uses the same canonical maps. See the
[exact-functor client](../examples/downstream/Consumer/ExactFunctor.lean).
The Serre interfaces `quotientKMap`, `connectingHom`, and `localizationSequence`
include the connective K₀ tail.

## Classical degree-zero presentation

For every exact category `E`, with independent object and morphism universes,
`Quillen.ExactStructure.grothendieckKZeroEquiv` identifies the object-generated
Grothendieck group modulo the original conflation relations with `E.K 0`.
Its forward map is `grothendieckToKZero` and its inverse is the genuine
`kZeroToGrothendieck` retraction. Both inverse identities, original object
classes, and all-class exact-functor naturality are retained.
`Quillen.KTheory.GrothendieckComparison.Equivalence` supplies the equivalence;
`GrothendieckComparison.Functor` supplies
`Quillen.SmallExactCategory.grothendieckFunctor` and `grothendieckKZeroIso` to
the existing `KFunctor 0`.

The Q proof uses the algebraic groupoid factorization and realization of the
genuine localization functor. Surjectivity uses compact open-cover subdivision,
collar deformation, original interval cells, the original-object zero skeleton,
and one-skeleton fullness. `Quillen.Topology.ClassifyingSpace.CompletionSurjectivity`
proves bijectivity of the original completed-loop map for any category; neither
edge-path generation nor a classical presentation is an input premise.

For small Waldhausen categories with matching object and morphism universes,
`Quillen.Waldhausen.GrothendieckComparison.Equivalence` identifies
`Quillen.Waldhausen.AlgebraicGrothendieck.Group W` with actual `W.K 0`.
`AlgebraicGrothendieck.grothendieckKZeroEquiv` has the original based object-loop
map as forward map and the original realized grading as inverse. It retains
the weak-arrow and displayed cofibration-pushout relations, both inverse
identities, and naturality on every class for every exact functor.
`Quillen.Waldhausen.KFunctor` includes exact functors that do not strictly
preserve the chosen zero; `SmallWaldhausenCategory.grothendieckKZeroIso` is the
bundled natural isomorphism. No cylinder, factorization, JointData, or
presentation premise is added.
The presentation comparisons retain their existing classifying-space,
Theorem B, and additivity proof dependencies.

`Quillen.Waldhausen.GrothendieckComparison.SmallModel` extends the equivalence
to independent object and morphism universes through actual up/down quotient
maps and the existing based realization homeomorphism.
`grothendieckKZeroEquivOfSmallModel` retains the original `Group W` and `W.K 0`
endpoints, original object classes, and both directions of exact-functor
naturality. Its inverse is the transported realized grading; it agrees with
the prior comparison when the universes match. The reusable
`Topology.Realization.ZeroSkeleton` and
`Topology.Realization.EdgePathPresentation.SimplicialFullness` owners supply genuine
vertices and characteristic paths, with continuous-path generation proved.

`Quillen.AlgebraicGeometry.PerfectComplexes.GrothendieckComparison` specializes
that small-model theorem to `perfectGrothendieckKZeroEquiv X` for every scheme
and literal `PerfectK X 0`. Its restriction laws require
`j : U ⟶ X` with `[IsOpenImmersion j]` and preserve all original classical and
homotopical classes. This is the weak-arrow/cofibration-pushout presentation;
the triangulated-derived presentation requires a separate comparison.
Bass recursions keep their original homotopical perfect K₀ seed. Localization
and Mayer–Vietoris use their own cofinality and fiber comparisons.

## Waldhausen interfaces

For `W : Quillen.Waldhausen.Structure C`, cofibrations, weak equivalences, and
zero are explicit data. `W.Delooping` realizes the diagonal S-construction
nerve, `W.kBasepoint` is its point, and `W.K n` gives the connective groups.
The Q/S comparison is in
`Quillen.Waldhausen.QuillenComparison.Equivalence`.

`Quillen.Waldhausen.Fibration.GeneralComparison` supplies the canonical fiber
comparison with nested weak equivalences, coarse two-out-of-three and extension,
joint-cylinder data, and the second-endpoint section identity.
`Quillen.Waldhausen.Fibration.LongExactSequence` supplies its maps and exactness statements.
Object and morphism universes may differ.
`Quillen.Waldhausen.GilletWaldhausen.GeneralComparison` compares bounded-term complexes with an
abelian term category whose term property contains zero and is closed under
isomorphisms, extensions, and admissible kernels.
`Quillen.Waldhausen.Cofinality.GeneralDense` keeps dense-cofiber closure and joint-cylinder data
explicit; positive equivalences and degree-zero tails have separate statements.

## Scheme and perfect-complex interfaces

For `X : AlgebraicGeometry.Scheme.{u}`, `Quillen.Scheme.K X n` uses vector
bundles and `Quillen.Scheme.G X n` uses coherent sheaves with the stated local
noetherian hypotheses. Both lie in `Type (u + 1)`;
`Quillen.Scheme.Affine.G R n` lies in `Type u`.
`Quillen.CoherentScheme.AffineFiniteType R` is the category of affine
quasicoherent sheaves with finite global-sections module, over any ring.
`Quillen.CoherentScheme.affineLocallyFiniteType X` tests quasicoherence and finite type on every affine
chart, and `FiniteTypeSheaves X` is defined over every scheme. Their Serre,
abelian, exact-category, and G-theory theorems retain their noetherian conditions.

`restrictK`, `restrictG`, and `KToG` are the canonical maps.
`pullbackK` and `KFunctor` accept all scheme maps; `pullbackG` requires flat
maps between locally noetherian schemes. Regular affine K→G has no finite
Krull-dimension bound. The nonaffine comparison requires quasi-compactness
and the resolution property, which regularity alone does not supply.

In `Quillen.PerfectComplexes`, `StrictPerfect X` consists of globally bounded
finite locally free complexes. `Perfect X` consists of complexes locally
isomorphic in quasi-isomorphism localization to strict perfect complexes.
`StrictK X n` and `PerfectK X n` are connective S-groups in `Type (u + 1)`.
`vectorBundleToStrictKEquiv` holds on every scheme, and affine strict/local
comparisons include every nonnegative degree. `strictKPullback` accepts every
scheme map; `perfectKPullback` and `PerfectKFunctor` accept arbitrary maps
between quasi-compact schemes and retain the existing restrictions.
The relative/support comparisons, qcqs endpoint, K₀ image, excision, and
Mayer–Vietoris interfaces are in [ThomasonTrobaugh.md](ThomasonTrobaugh.md).

### Finite pushforward

Geometric paths in this subsection have prefix `Quillen.AlgebraicGeometry`.
`Scheme.FinitePushforward` gives `Quillen.Scheme.GFinitePushforwardFunctor`
for actual finite morphisms of locally noetherian schemes. Its maps are the
canonical small-K maps of coherent direct image, with exactness and identity,
composition, scheme-isomorphism, and open-base-change laws in
`Scheme.Coherent.Finite`. Finite-type quasicoherent preservation itself has
no noetherian hypothesis. The finite-affine and closed-immersion specializations
are the existing original functors and G-maps.

`Scheme.FiniteFlatPushforward` gives `KFiniteFlatPushforwardFunctor` for finite
flat maps of locally noetherian schemes. Target noetherianity makes the affine
finite flat modules finite projective; exactness is transported through the
coherent inclusion. `Scheme.Comparison.KToGFinitePushforward` gives the natural
transformation `KToGFiniteFlatPushforward` with the original K→G maps.
`PerfectComplexes.FiniteFlatPushforward` constructs strict-perfect direct image
and `strictKFiniteFlatPushforward`; `FiniteFlatPushforwardNaturality` retains
`vectorBundleToStrictKMap` in every nonnegative degree. Quasi-isomorphism
preservation uses exact coherent direct image. These statements do not assert
proper pushforward or finite-flat vector-bundle preservation over arbitrary
nonnoetherian bases.

### Derived direct image and base change

The following routes have prefix `Quillen.AlgebraicGeometry.Scheme.Sheaf`.

| Owner | Current interface |
| --- | --- |
| `AffinePushforwardAcyclicity`, `AffineDerivedPushforward`, `AffineBoundedDerivedPushforward` | Quasicoherent sheaves are acyclic for affine direct image; the installed D+ unit is invertible on singles and bounded termwise-quasicoherent complexes |
| `FlatInjectivePushforward` | Flat direct image preserves injective targets and gives the actual bounded-below injective derived-Hom adjunction |
| `FlasquePushforwardAcyclicity`, `FlasqueDerivedPushforward`, `FlasqueComplex`, `FlasqueComplexDerivedPushforward` | Flasque sheaves are acyclic for every scheme map; direct image preserves quasi-isomorphisms of bounded-below flasque complexes, with invertible installed unit and no upper bound |
| `DerivedPushforwardComposition` | Canonical `R(g ∘ f)_* ≅ Rg_* Rf_*` on bounded-below derived categories, retaining ordinary composition and both unit equations |
| `DerivedOpenBaseChange` | D+ open base change for arbitrary scheme morphisms, with the original module-sheaf comparison and derived-unit equation |
| `AffineCompositeDerivedPushforward` | Installed unit invertible on `j_*M` singles when `j` and `j ≫ f` are affine and `M` is quasicoherent |
| `CartesianBaseChange`, `AffineScalarAdjunction`, `AffineScalarSquare`, `AffineBaseChange` | Ordinary geometric/scalar mates and invertibility for quasicoherent sheaves on genuine cartesian squares of spectra |
| `CartesianBaseChangePasting`, `CartesianBaseChangeHorizontal`, `CartesianBaseChangeLocalization` | Vertical/horizontal ordinary mate equations and open-cover detection of invertibility, with local hypotheses explicit |
| `DerivedFlatBaseChange`, `DerivedFlatBaseChangeShift`, `DerivedFlatBaseChangeHorizontal`, `DerivedFlatBaseChangeVertical`, `DerivedFlatBaseChangeLocalization`, `DerivedOpenCoverConservativity`, `DerivedFlatBaseChangeOpenCover` | Canonical bounded-below derived flat mate, unit and shift equations, pasting, target-open localization, and cover conservativity |
| `CartesianOpenBaseChangeMate`, `DerivedFlatBaseChangeOpen` | The same mate is invertible on every bounded-below complex when the base leg is an open immersion |
| `AffineDerivedBaseChange`, `AffineDerivedBaseChangeCoordinates`, `AffineDerivedBaseChangeLocal` | The same mate is invertible on quasicoherent singles and their integer shifts for affine morphisms and flat base change, including arbitrary affine coordinates and nonaffine ambient schemes |
| `AffineCompositeDerivedBaseChange`, `TwoOpenDerivedBaseChange` | Transport of that mate through actual chart images and the signed two-open derived triangle |

Affine acyclicity imposes no finite, flat, or noetherian condition. Ordinary
affine quasicoherent base change imposes no flatness or finite-generation
condition. Derived flat base change retains the genuine cartesian square and
flat base leg; exact pullback preserves homology without an injective-preservation
assumption. Its general bounded-below invertibility is distinct from the
QC-single and open-base-change specializations. Composition alone does not
supply triple-composition coherence.

`Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPushforwardComparison`
identifies strict finite-flat direct image with the installed D+ direct image
on locally noetherian schemes. `PerfectComplexes.Affine.DerivedFiniteFlatPushforward`
preserves intrinsic D+ perfectness for affine source and finite flat map to a
locally noetherian target. General-source preservation and unrestricted unbounded
derived pushforward remain open. Generic bounded induction, exact-functor homology,
single triangles, and right-derived composition/shift/identity live under
`Quillen.Algebra.Homology`, notably `DerivedCategory`.
The precise mathlib derived-functor owner is accessed by supported `import all`
where its public unit contains a hidden proof constant; no private declaration
is named and no mathlib source is modified.

### Tensor and projective-line geometry

`Quillen.Algebra.Category.ModuleCat.Sheaf.Tensor` constructs the sheafified
tensor bifunctor and left unit with both variance maps and unit naturality;
site and universe hypotheses are explicit. `TensorExact` proves additivity and
short exactness for actual finite-free coefficient retracts, including empty
finite coproducts. `Scheme.Sheaf.TensorRestriction` gives the genuine
open-immersion restriction isomorphism. `Scheme.VectorBundle.TensorLocalExactness`
uses affine finite-free retractions to prove exactness for finite locally free
coefficients. Full monoidal coherence is a separate interface.

`Scheme.VectorBundle.ProjectionFormula` gives the ordinary projection formula
for every scheme map, arbitrary source module sheaf, and finite locally free
target coefficient. Its arrow is the geometric adjunction-unit composite.
`DerivedProjectionFormula` gives the bounded-below derived natural isomorphism,
retaining the ordinary arrow and installed units, without an upper bound or
an extra global flasqueness hypothesis. These geometric paths have prefix
`Quillen.AlgebraicGeometry`.

`Quillen.Scheme.ProjectiveLine.twoChartLine R` glues two polynomial charts
along the Laurent overlap over every commutative ring. It is qcqs, its projection
is flat and separated, and `globalSectionsIso R` identifies its sections with
`R`. The current projective-line routes have prefix
`Quillen.AlgebraicGeometry.Scheme.ProjectiveLine`:

| Owners | Interface |
| --- | --- |
| `Charts`, `GlobalSections`, `AffineCechCover`, `CechDifference`, `ChartAffineness`, `BaseChangeGluing` | Original chart maps, affine intersections, signed Laurent restriction, affine chart immersions, and cartesian coefficient changes |
| `Cohomology`, `StructureSheafCohomology`, `TautologicalCohomology`, `TautologicalQuotientCohomology` | Actual derived section computations for quasicoherent sheaves, structure module, tautological line, and quotient |
| `Tautological`, `TautologicalSections`, `TautologicalQuotient` | Line columns `(1,t)` and `(s,1)`, Laurent transition `T` with inverse `T⁻¹`, quotient rows `(-t,1)` and `(-1,s)`, and the original short exact sequence |
| `TwistMinusFunctor`, `TwistMinusUnit`, `VectorBundleTwistMinus` | Exact kernel negative-twist functor, structure-module identification, finite-local-freeness preservation, and original vector-bundle K-map |
| `StructureSheafDirectImage`, `TautologicalDirectImage`, `DerivedDirectImage`, `VectorBundleDirectImage`, `VectorBundleComplexDirectImage`, `DerivedCechTriangle` | Canonical projection units, structure/negative-line direct images, affine bundle and bounded-complex comparisons, and the relative signed Čech triangle |
| `DiagonalIncidence`, `DiagonalMonomorphism`, `DiagonalClosedImmersion`, `DiagonalCokernel` | Four original scalars `t-u`, `tv-1`, `1-su`, `v-s`, the closed relative diagonal, and the twisted short exact sequence |
| `DiagonalTensorTriangle`, `DiagonalBundleTensorTriangle`, `DiagonalTensorPushforward`, `DiagonalDerivedTensorTriangle`, `DiagonalProjectedTensorTriangle` | Original tensor triangles, diagonal-supported identification, installed derived diagonal image, and derived second-projection triangle |
| `DerivedFlatBaseChange` | Canonical QC-single derived flat base change for the original projection and its actual self-base-change square |

For every quasicoherent sheaf, actual derived global sections vanish above
degree one. The structure module and tautological quotient have no positive
cohomology; the negative tautological line has zero cohomology in every degree,
including zero. Quotient global sections are `R × R` through the original
projection. The relative projection statements retain the given injective
resolution and installed D+ unit: structure-module direct image is canonically
the base structure module, and the negative line has zero derived direct image.
For affine-base vector bundles the geometric unit is invertible, and the
negative twist has zero D+ image; bounded-complex versions retain the original
degreewise unit. The relative Čech computation and flat base change are for
quasicoherent singles. These results include nonreduced and zero rings.

The diagonal sequence is the actual twisted sequence
`p₁*L → p₂*Q → Δ_*Q`; its quotient is the cokernel of the incidence.
Tensoring by any projective-line vector bundle retains incidence, quotient, and
connecting maps. After derived second projection, the third vertex is the
single of `E ⊗ Q`; the first two remain actual derived-image objects.
Proj identification, the full twisting-sheaf family, tensor identification of the
kernel twist, coefficient perfection, and projective-bundle generation remain
open. The finite-coefficient retract criterion in
`Quillen.Algebra.Module.FiniteCoefficientRetract` retains its projectivity,
splitting, and uniform finite-window premises; no production application supplies
the missing perfect-pushforward conclusion.

## Connective spectra

`Quillen.LoopPrespectrum` has based spaces and continuous maps `Eₙ → ΩEₙ₊₁`.
`Quillen.Waldhausen.IteratedS.originalPrespectrum W` uses the iterated
S-construction and original cylinder transitions; `originalPrespectrum_isOmega`
proves its Ω condition. For integer `d`,
`Quillen.LoopPrespectrum.stableHomotopyGroup E d` is the
additive colimit of

```text
π_(d.toNat + n + 2)(E_((-d).toNat + n + 2)),  n : ℕ.
```

`Quillen.Topology.Prespectrum.StableOmega` supplies `stableHomotopyStageZeroIso`
for Ω-spectra. In `Quillen.Waldhausen.IteratedS`, `originalKStableEquiv W n`
is an additive equivalence from `Additive (W.K n)` in every nonnegative degree,
including K₀. The older `originalZeroSpaceEquiv` is a set equivalence.
`originalStableHomotopyGroup_neg_subsingleton` gives negative vanishing.

`exactOriginalPrespectrumMap` and `exactOriginalOmegaSpectrumMap` normalize
arbitrary exact functors at zero while retaining public `KMap`.
`exactStableKMap` has identity, composition, and weak-transformation laws;
`originalKStableEquiv_exact_naturality` has no chosen-zero equality premise.
Normalized identity/composition and weak transformations give whole based
prespectrum homotopies. `SConstruction.Iterated.ExactModelEquivalence` keeps a
zero-preserving forward exact equivalence, normalizes its inverse, and gives
whole unit/counit homotopies, including level zero and unequal hom universes.

### Composition and object tracks

`Quillen.CategoryTheory.TheoremB.CompositionHomotopy` derives relative realized
composition tracks from the genuine transformation two-simplex.
`Quillen.Waldhausen.SConstruction.NerveTriangle`, `WeakGridTriangle`, and
`WeakNaturalTransformationTriangle` retain all three original cylinder faces.
The `Iterated.NaturalTriangle`, `TriangleStructure`, `TriangleRealization`,
`PrespectrumCompositionHomotopy`, and `PrespectrumPastingHomotopy` owners lift
these to whole relative prespectrum comparisons. `NormalizationNaturality`,
`NormalizationPasting`, and `NormalizationTrackPasting` retain actual chosen-zero
whiskering and relative pastings. Comparison, path/loop, and structure parameters
remain independent, including degree-zero loops.

`Quillen.Topology.ClassifyingSpace.ArrowPaths` exposes data-valued simplex and
edge-composition homotopies. `Quillen.Waldhausen.Fibration.WeakObjectTrack`
retains the two original weak-arrow triangles and common diagonal;
`SConstruction.ObjectTransformationTrack` evaluates transformation cylinders
on object loops; `Fibration.CanonicalFiberObjectLoop` retains both fiber
coordinates and the reversed zero-to-acyclic track. The
`Waldhausen.Additivity.ChangeWeakDeformation`, `ChangeWeakMixedHomotopy`,
`ChangeWeakEndpointHomotopies`, and `ChangeWeakBasedHomotopy` owners transport
the original mixed grids and subdivided based additivity deformation under
enlargement of target weak equivalences, with the actual cofibration premise.

## Stable fibers and localization

In `Quillen.LoopPrespectrum`, `parameterLooping` transposes loop and structure
coordinates. `parameterStableHomotopyIso` has stage sign `(-1)^n` and
`parameterStableOffset d`, one for `d < 0` and zero otherwise. It is distinct
from `looping` and the older square-cone construction.
`homotopyFiber f` is an actual path-space prespectrum; Ω inputs give an Ω fiber
with the component conditions. For every prespectrum map,
`stableFiberLongExactSequence` gives the integer-degree segment

```text
π^st_(d+1)(E) → π^st_(d+1)(F) → π^st_d(Fib f) → π^st_d(E) → π^st_d(F).
```

The boundary uses the inverse signed parameter-loop shift and literal
loop-to-fiber inclusion. Whole coherent based squares give fiber maps and
boundary naturality. Vanishing of all integer fiber groups detects stable
equivalence. A fiber of connective inputs is connective under K₀ surjectivity.
`Quillen.Waldhausen.Fibration.SpectrumComparison` supplies the canonical stable
fiber comparison `canonicalFiberPrespectrumMap_isStableEquivalence_general`
and that surjectivity with coarse two-out-of-three, extension,
joint data, and second-endpoint section.

`CoherentHomotopyCategory` quotients by whole coherent based homotopies;
`StableLocalization` then inverts all-integer stable equivalences.
`localizedStableHomotopyFunctor` descends stable groups with a universal lift.
In `Quillen.Waldhausen.IteratedS`, `localizedSpectrumMap` has literal identity
and composition and weak-transformation invariance; `localizedSpectrumMapIso`
requires bijectivity of every original K-map, including K₀.
`Quillen.PerfectComplexes.PerfectLocalizedSpectrumFunctor` is contravariant for
arbitrary maps between quasi-compact schemes, inverting the bounded-flat
inclusion and retaining original K-maps and flat pullback.
`BoundedFlatLocalizedSpectrumFunctor` accepts all schemes; its route is
[Spectrum/DerivedPullback.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean).
The localized inverse does not give a strict continuous inverse. A standard
stable model structure, triangulation, and fullness of the localization remain
separate claims.

### Cones, pushouts, and finite excision

The routes in this subsection have prefix `Quillen.Topology`, unless indicated.
`Prespectrum.ConeHomotopySquare` and `PushoutHomotopySquare` retain supplied
whole square tracks and the original target cylinders. `RelativeHomotopy`,
`PushoutHomotopy`, `PushoutMovingHomotopy`, and `HomotopySquareOfPasting`
descend actual two-parameter relative comparisons or moving squares, retaining
their four faces and independent structure time. Equality of stable maps alone
does not supply these squares or higher coherence.

For `f : E ⟶ F`, the canonical `mappingConeFiberComparison f` is the map
`E ⟶ homotopyFiber (mappingConeInclusion f)`, with the original cone cylinder
as its full fiber path. Cone-fiber excision below means stable equivalence of
this same source-to-fiber map.

Chosen-point HEP makes reduction of the ordinary cone or double cylinder a
homotopy equivalence and is preserved by the reduced construction.
`Prespectrum.PushoutWeakEquivalence` and the cone whole-track weak-invariance
owners keep complete weak vertex maps and their point-HEP premises explicit.
`Path.PointHEP`, `Prespectrum.ParameterLoopingPointHEP`, and
`HomotopyGroups.Loop.WeakEquivalence` preserve actual point HEP for closed
points and complete weakness of based loops, including every component.
`Prespectrum.ConeHomotopyExactness` gives strict mapping-out data and
contravariant exactness in the coherent homotopy quotient. Its transfer to stable
localization is a separate question. The identity cone is coherently contractible;
complete positive-level weak arrows with chosen-point HEP have a stably trivial
cone and complete positive-level weak cone-fiber comparison.

`HomotopyGroups.Connectivity.Basic` uses nonempty actual fibers and all-point
homotopy triviality below a finite bound. `HELP.Connectivity`,
`Cube.RadialExpansion`, `Cube.ThinSupport`, `Cube.BoundaryHomotopyNormalization`,
and `CubicalSubdivision.{ConnectivityLifting,ColumnAvoidance,FaceNormalization,TwoChartGridNormalization}`
supply finite cube HELP and global incident-face normalization with the entire
prescribed boundary track. `HomotopyPullback.OverlapConnectivity` and
`DoubleMappingCylinder.{CollarConnectivity,ColumnNormalization,CollarGapConnectivity,GapConnectivity}`
give the genuine finite gap bound: if the two maps are `p`- and `q`-connected,
the original gap is `r`-connected when `r + 1 ≤ p + q`, including fiber
nonemptiness and every fiber point. The double-cylinder theorem adds no
separation, CW, attaching-cofibration, or connectivity-growth premise. Finite
cube HELP still does not imply arbitrary compact HELP.

`Quillen.Waldhausen.SConstruction.Iterated.FiniteConnectivity` proves the
original S-level growth: level `n+1` has vanishing homotopy sets through degree
`n` at every point. `Iterated.ConeFiberExcision` uses that growth, actual point
HEP, and the finite gap to prove stable cone-fiber equivalence for any original
S-model map. `Prespectrum.ConeLinearExcision` gives an explicit linear-growth
criterion. `ConeStableExactness` and `ConeStableNaturality` transport the fiber
sequence through the same comparison, with original cone inclusion and signed
boundary. Whole-track stable cone/pushout invariance retains its row-excision
premises in `ConeHomotopySquareStableExcision` and
`PushoutHomotopySquareStableEquivalence`; concrete Model and finite Bass-stage
owners discharge them. General stable cone excision for arbitrary prespectra is
not supplied by these specializations.

### Telescopes and Ω replacement

The following routes have prefix `Quillen.Topology.Prespectrum`.

| Owners | Current interface |
| --- | --- |
| `TelescopeCompactness`, `TelescopeRepresentability`, `TelescopeHomotopyColimit`, `TelescopeStableColimit` | Original stage inclusions, compact finite-stage representatives, eventual equality, and homotopy/stable colimit comparisons for T1 stages |
| `TelescopeHomotopy`, `TelescopeHomotopyMap`, `TelescopeMovingHomotopy`, `TelescopeHomotopyMapIdentity`, `TelescopeHomotopyMapComposition`, `TelescopeStableMapExt` | Strict or track-defined maps, moving-square descents, actual identity/composition homotopies, and stable-map detection by stage inclusions |
| `TelescopeStableEquivalence`, `TelescopeStableExactness` | Stagewise stable equivalences and explicit stagewise exact sequences descend to signed stable groups |
| `TelescopeConeIso`, `TelescopeConeStableColimit`, `TelescopePushout`, `TelescopePushoutIso`, `TelescopeStrictSquare` | Strict cone/pushout interchange retaining original cylinder coordinates, and stable cone-colimit comparison with T1 premises |
| `TelescopeParameterLooping`, `TelescopeParameterLoopingStable`, `TelescopeTail` | Actual parameter-loop comparison and tail maps with their signed stable equations |
| `StableStabilization`, `LoopTailOmega`, `LoopTailReplacementFunctor`, `LoopTailReplacementStableNaturality`, `LoopTailReplacementFiberEquivalence`, `StableOmegaLevelDetection` | Strict loop-tail Ω replacement, natural stable unit, fiber comparison, and all-level weak detection |

Reduced telescopes of T1 stages are T1, with original stage inclusions closed
embeddings. Compact relative maps and whole homotopies have representatives at
common finite stages with exact transition endpoints. Their original homotopy
groups, including degree zero, and all integer stable groups are the canonical
sequential colimits. Track-defined stable maps agree with the colimit maps;
stagewise exactness remains an explicit hypothesis of the generic exactness
theorem. Canonical telescope identity/composition homotopies fix each original
stage and require no T1 condition; higher coherence between them is separate.
Strict cone and pushout interchange require neither separation nor point HEP.
Parameter-loop interchange is a stable equivalence for T1 stages and preserves
independent loop time and cylinder height.

The unchanged stabilization `E → looping(tail E)` is an all-integer stable
equivalence. Its actual iterated telescope is Ω under levelwise T1, with complete
weak structure adjoints at every source point and target-component coverage.
The replacement is a strict functor without T1; under source/target T1 it
preserves and reflects stable equivalences and commutes with fibers by an actual
stable, all-level complete weak comparison. A strict map between genuine
Ω-prespectra is stable exactly when every level is completely weak, without T1
or connectedness assumptions. Thus the replacement unit is levelwise weak on
already-Ω T1 inputs; the unit on an arbitrary input and cofiber preservation
remain separate claims.

## Bass groups and the affine transition

`Quillen.PerfectComplexes.Bass.negativeKFunctor n` is contravariant on
quasi-compact schemes, with `n : ℕ` denoting degree `-n`. The seed is additive
homotopical `PerfectK X 0`; successors are actual two-polynomial-to-Laurent
cokernels with quotient, exactness, and descent APIs.
`Bass.supportedNegativeKFunctor` uses supported perfect K₀ on pairs with
quasi-compact ambient base and arbitrary vanishing open.
`Quillen.Bass.negativeKFunctor` is the ring interface;
`Quillen.Bass.affineSchemeNegativeKIso` compares it naturally with the scheme
recursion in all nonpositive degrees, with literal original K₀ at zero.
`Quillen.KTheory.Bass.RightExactness` and `IterationExactness` preserve
pointwise right exact sequences and cokernels through the original contraction
and all existing ring-indexed iterates. They supply no negative localization
boundary.

### Raw geometric step and section evaluation

`Quillen.PerfectComplexes.affineBassTransition` uses Laurent `T¹` and `T⁻¹`,
the original scalar action, and its structure-compatible whole homotopy. The
raw bounded-flat pullback is defined for every scheme map in
`Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatPullback`;
`Spectrum.FlatSquare` retains the original flat-square homotopies.
For the remaining routes in this section, `BoundedFlat` and `Affine` have
prefix `Quillen.AlgebraicGeometry.PerfectComplexes`.

`BoundedFlat.{Pseudofunctor,PullbackCoherence,NormalizedPullbackCoherence,TripleTrack}`
retains geometric composition, actual binary zero normalizations, and whole
relative associativity for the preexisting tracks. `Affine.BassSpanMap` handles
flat ring coefficient changes; `BoundedFlatBassSpanMap`, `BoundedFlatBassSquare`,
`BassSpanComparisonTrack`, and `BoundedFlatBassTransitionNaturality` construct
the original raw coefficient maps and whole comparison/seed homotopies for
arbitrary coefficient changes. The Laurent unit/null moving squares retain both
chart endpoints, fixed cone point, and independent comparison, loop, and
structure times. The relevant Laurent owners include
`BoundedFlatLaurentUnitSquareHomotopy`, `BoundedFlatLaurentUnitTrack`, and
`BoundedFlatBassNullSquare`.

`Affine.BassInclusionComparison` constructs
`boundedFlatPerfectBassComparisonHomotopy` from the original chart pastings.
`BassGeometricComparison` proves that the same cone and parameter-looped step
maps are complete weak equivalences at positive levels and stable in every
integer degree, with no supplied geometric compatibility premise.
`BassTransitionInclusion` gives `boundedFlatPerfectBassTransitionHomotopy`
between the unchanged original seeds. On quasi-compact schemes the underlying
bounded-flat inclusion is completely weak at every positive level, using its
Ω structures and component coverage; original S-vertices have point HEP,
including level zero. These statements do not choose a continuous inclusion
inverse.

`BoundedFlat.Sections` forms cocartesian sections of the geometric Grothendieck
construction. `SectionEquivalence`, `SectionZero`, `SectionWaldhausen`, and
`SectionReindexExact` retain identity evaluation, canonical pullback sections,
one global chosen zero, and exact coefficient reindexing. Objects and morphisms
of the section category both have universe `u+1`, although original bounded-flat
morphisms have universe `u`. `SectionSpectrumEquivalence` and
`SectionPrespectrum` supply all-level homotopy equivalence and a genuine strict
coefficient diagram of iterated-S models. Evaluation preserves original K-maps.

`SectionEvaluation`, `SectionEvaluationNormalization`, `SectionSpectrumNaturality`,
`SectionModelComposition`, `SectionModelRelativeComposition`,
`SectionModelTrackNaturality`, `SectionModelTargetTrack`, and
`SectionCoefficientComposition` keep actual cocartesian transition isomorphisms,
chosen-zero/common-universe transports, and whole coefficient and composition
tracks. Their generic categorical owners are
`Quillen.CategoryTheory.FiberedCategory.CocartesianSectionComposition`,
`CocartesianEvaluationCoherence`, and `CocartesianEvaluationNormalization`;
small-model coefficient coherence/pasting is under `Quillen.Waldhausen.SmallModel`.

`Affine.SectionBassEvaluation` gives the strict-section-to-raw span, cone, and
looped-step maps with their full geometric filler.
`SectionBassEvaluationEquivalence` proves those same maps completely weak at
every level, including zero, and stable in every integer degree.
`SectionBassEvaluationNull`, `SectionLaurentEvaluationHomotopy`,
`SectionBassSeedEvaluation`, and `SectionBassPerfectSeedEvaluation` compare the
original null tracks, Laurent units, and single raw/perfect seeds, without a
seed-compatibility hypothesis. These single-step and single-seed squares do not
identify the full original geometric tower.

### Strict finite stages, bottom groups, and telescope

`Quillen.KTheory.Bass.StrictDiagram` uses the literal polynomial/Laurent square
to define a Bass endofunctor on strict spectrum-valued diagrams and strict
natural transformations. `StrictDiagramStableEquivalence` retains explicit
growth/HEP hypotheses; `ModelDiagramStableEquivalence` discharges them for
genuine iterated-S Model diagrams and exact-equivalence maps.
`Affine.SectionLaurentUnit` and `SectionLaurentPullback` supply the original
termwise `h(T)` and `h(T⁻¹)` action. `SectionBassSeed` is the actual natural
transformation `F → B(F)`, and `SectionBassTransition` gives every transition
as `B^i` of this same Laurent seed. `SectionBassDiagram` and
`SectionBassTelescope` retain strict coefficient laws and all original cylinders.

| Affine owners | Current comparison |
| --- | --- |
| `SectionBassConnectivity`, `SectionBassConeExcision`, `SectionBassWholeTrackCone` | Finite-stage all-point growth and actual cone-fiber excision, retaining strict or whole-track arrows |
| `SectionBassPushoutCollapse`, `SectionBassPushoutExcision`, `SectionBassPushoutStableEquivalence`, `SectionBassPushoutHomotopyStableEquivalence`, `SectionBassFunctorStableEquivalence`, `SectionBassIterateStableEquivalence` | Stable preservation of the original finite-stage pushout/Bass maps from explicit stable corner maps |
| `SectionBassStableSequence`, `SectionBassTelescopeCone`, `SectionBassTelescopeExcision`, `SectionBassTelescopeNaturality` | Signed exact cone sequences for finite stages and the actual telescope coefficient map, with natural original boundary |
| `BoundedFlatBassSpanStableGroups`, `BoundedFlatStableKZero`, `BassFirstCokernel`, `BassFirstStableGroup`, `BassFirstStableNaturality`, `SectionBassFirstStableGroup` | Original raw first-step Laurent cokernel and degree-minus-one isomorphism, raw coefficient naturality, and evaluation transport to the strict first stage |
| `SectionBassStableConnectivity`, `SectionBassSuccessor`, `SectionBassSuccessorStable`, `SectionBassBottomGroups`, `SectionBassBottomCokernel`, `SectionBassBottomComparison` | Natural comparison of `negativeKFunctor i` with degree `-i` at finite stage `i`, preserving the recursive Laurent quotient and chart signs |
| `SectionBassStableColimit`, `SectionBassNegativeMap` | Canonical all-integer telescope colimit and natural maps from the original negative groups through stage inclusions |
| `SectionLocalizedComparison`, `SectionBassLocalizedSpectrum` | Natural initial map from the original localized perfect spectrum to the actual Bass telescope |
| `SectionBassTelescopeLooping`, `SectionBassTelescopeCommutation`, `SectionBassTelescopeSelfMap`, `SectionBassTelescopeSelfMapIdentification` | Actual Bass/telescope comparison and the coefficient-natural stable self-map to the telescope's Bass image |

At stage `i`, original level `n+i+2` has vanishing homotopy sets in degrees
`k < n+2` at every point. The stage has no stable groups below `-i`; its
polynomial span is generated at degree `-i` by the two original inclusions.
For maps between stages `i,j`, cone-fiber comparison has connectivity
`2*n+2` at level `n+max(i,j)+2` and is an all-integer stable equivalence.
The original signed boundary and all three recurring exactness positions are
retained. Finite exact colimits discharge the actual telescope coefficient
cone-sequence hypotheses; no uniform whole-telescope connectivity is assumed.

`Quillen.Topology.Prespectrum.ConeStableCokernel` and
`Quillen.KTheory.Bass.{TwoChartSigns,TwoChartStableCokernel}` retain the Laurent
representative, negate only the second polynomial summand, and use the genuine
signed parameter-loop shift. `BassFirstStableGroup` compares existing
PerfectK-based `negativeKFunctor 1` with raw first-step degree minus one;
`BassFirstStableNaturality` uses the original raw coefficient stable maps.
The all-stage bottom comparison is a natural isomorphism at stage `i`, degree
`-i`; comparison with the earlier evaluation-based first-stage isomorphism
remains separate.

`SectionBassNegativeMap` composes that finite-bottom isomorphism with the
original stage inclusion into the telescope, retaining coefficient, Laurent
quotient, and next-stage seed/cylinder formulas. It supplies neither injectivity
nor surjectivity. The initial localized perfect-spectrum map likewise does not
assert nonnegative-group isomorphisms. Bass/telescope commutation and the tail
map give a stable self-map from the original telescope to its own Bass image
in every integer degree; its initial face is the original Laurent seed followed
by Bass of the original initial inclusion. No finite transition is assumed
stable. Fixed-degree transition stabilization and classical telescope negative
identification remain open.

### Fixed-open support and the localization comparison

For `j : U ⟶ Spec R` with `[IsOpenImmersion j]`,
`Quillen.AlgebraicGeometry.Scheme.Affine.OpenPairBaseChange` chooses its actual
pullback over every object of `Under R`. Coefficient lifts have both projection
equations and strict laws between these endpoints. At the identity algebra the
projection is an isomorphism to `j`, rather than equality of independently
chosen opens. `Quillen.Algebra.Polynomial.LaurentUnderSquare` retains the literal
positive/inverse Laurent legs.

`BoundedFlat.{SupportedSections,SupportedSectionReindex,SupportedSectionUnit,SupportedSectionZero}`
restricts the section objects to acyclicity on that specified open.
`SupportedSectionEquivalence`, `SupportedSectionWaldhausen`,
`SupportedSectionCoefficientIso`, `SupportedSectionReindexExact`, and
`SupportedSectionModel` give original exact coefficient maps, pushouts, and
chosen zeros, without flatness, cartesianness, or quasi-compactness assumptions.
`SupportedSectionComparison` normalizes evaluation by the canonical zero-object
isomorphism; `SupportedSectionSpectrumEquivalence` gives actual inverse maps
and whole homotopies, including level zero and all components.
`SupportedSectionModelNaturality` supplies the whole geometric coefficient
track, not strict evaluation naturality.

`BoundedFlat.SupportedSectionDiagram`, `SupportedSectionUnitHomotopy`,
`Affine.SupportedSectionLaurentUnit`, `SupportedSectionDiagramLaurent`, and
`SupportedSectionBassSeed` give the genuine fixed-open strict diagram and
literally coefficient-natural Laurent seed. No supplied seed/coherence premise
remains. The separately expanded evaluated-term scalar transfer is not used as
a hypothesis. `BoundedFlat.{SupportedSectionForgetEvaluation,SupportedSectionForgetExact,SupportedSectionForgetModel}`
and `Affine.SupportedSectionForgetLaurent`, `SupportedSectionForgetSeed` retain
the actual support inclusion and prove its whole Laurent and strict seed square.
`Quillen.KTheory.Bass.StrictUnderDiagram` preserves iteration under
`Under.forget`.

`Affine.SupportedSectionBassTower` and `SupportedSectionBassForgetTower`
construct the actual supported tower/telescope and maps to all ambient stages
and the ambient telescope. `SupportedSectionBassTelescopeSelfMap` is stable
at every coefficient and integer degree, with T1 premises discharged by the
original supported Model and Bass topology.
`SupportedSectionBassTelescopeSelfMapForget` proves its whole square with the
unchanged ambient self-map and actual forgetting arrow. The identity algebra
continues to use the actual pulled-back open.

`BoundedFlat.{SectionOpenStructure,SectionOpenWeak,SectionOpenEquivalence,SectionOpenComparison}`
compares the section coarse relative-open model with the original geometric
coarse model by exact evaluation and all-level homotopy equivalence.
`SupportedSectionOpenNull` retains the reversed zero-to-supported-section track
and its literal cone descent. `BoundedFlat.OpenConeComparison` proves the
geometric acyclic-support cone stably equivalent to the coarse relative-open
S-prespectrum. Stability of the supported-section cone and replacement by all
perfect complexes of the open are separate obligations, with the honest K₀
image endpoint retained.

`PerfectComplexes.OpenConeFiberLoop`, `Affine.PolynomialScalarCone`, and
`PerfectComplexes.ScalarCofiber` construct the supported cone of the original
global scalar, invertible on the specified Laurent open, and compare its
categorical cofiber and relative-acyclic K₀ class through the canonical fiber
map. `Quillen.CategoryTheory.Limits.CokernelPushout` retains the displayed zero;
`Quillen.Algebra.Homology.MappingConeSign` identifies `Cone(-f)` with `Cone(f)`
by negating the shifted source and fixing the target.
`Quillen.Waldhausen.SplitComplexes.FactorizationSign` and `FactorizationCofiber`
retain the original factorization quotient and target inclusion. This class
transport does not prove the Laurent-unit boundary identity, relative-loop
basepoint translation, or zero-section pushforward-class formula. Blanket
perfect zero-section dévissage and omission of possible Nil terms are not
asserted. See [ThomasonTrobaugh.md](ThomasonTrobaugh.md#remaining-obligations).

## Ring plus comparison and original components

`Quillen.KTheory.Plus` is the selected public facade for the homological plus
certificate, original Q-loop weak equivalence, positive comparison naturality,
and completion/telescope component classification. The individual imports below
are available when only one of those interfaces is needed.

Use `Quillen.KTheory.Plus.ProjectiveCompletionPositiveKNaturality` for
`StableCompletion.zeroCompletionPositiveKEquiv_baseChange`, the exact positive
comparison square with original maps and displayed path corrections.
`Quillen.KTheory.Map.RightBaseChange` gives the original KMap identity and
composition laws. The common ring universe is arbitrary; right modules use
left modules over the opposite ring.

`Quillen.KTheory.Plus.ProjectiveCompletionZerothHomotopy` provides
`completionZerothHomotopyKZeroEquiv`, its original object-class formulas, and
naturality for the continuous completion map and original KMap₀.
`Quillen.KTheory.Plus.ProjectiveTelescopeKZero` provides
`StableFreeRight.telescopeZerothHomotopyKZeroEquiv` and the exact original
stage formula `[P] - [rankOnePower n]`.

The independently compiled `Consumer.RingPlusNaturality` exercises the literal
positive square, corrected identity/composition, original K₀ object classes,
a noncommutative matrix ring, and a map to the zero ring. These interfaces do
not identify matrix-image ring change with a separate tensor-product functor,
or assert a natural whole-space splitting; see [Scope.md](Scope.md).

## Scalar extension of original right modules

Import `Quillen.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUniversal`
for `rightBaseChangeUnit`, `rightBaseChangeHomEquiv`, `rightBaseChangeLift`, and
`rightBaseChange_existsUnique`. These use the constructed matrix-image
functor and quantify arbitrary ambient target modules. Both source and target
naturality retain the displayed unit and actual maps. Rings and ambient target
modules may have independent universes; commutativity and flatness are absent.

The lower-level owners are `Quillen.Algebra.Matrix.RightScalarExtension` for
finite free modules and `Quillen.Algebra.Category.ModuleCat.MatrixImageScalarExtension`
for idempotent images. The independent `Consumer.RingScalarExtension` exercises
the exact public universal property, including a noncommutative ring and an
actual map to the zero ring. This is a Hom-universal characterization of scalar
extension; a separate literal balanced-tensor carrier comparison is not supplied.

## Client examples

The [downstream package](../examples/downstream) exercises public interfaces
through its local path dependency, configuration, manifest, and build directory.
The maintained [tests](../Tests) cover further constructions and regressions.
Neither directory is a dependency of library source. Verification conditions
and the complete check command are in [Scope.md](Scope.md#verification).
