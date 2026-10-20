# Derived operations on scheme-module complexes

## Local candidate interfaces

These candidates reuse the pinned Aglib derived localization and restriction interfaces.
ExtensionByZero retains its genuine localized adjunction, shift/triangulated structures and
literal unit/counit. RestrictionIsomorphisms retains original full faithfulness and zero detection
along scheme isomorphisms. InjectivePushforwardAdjunction/Comparison retain their all-sheaf
sources, lower-bounded injective targets and actual normalized derived Hom maps.

Affine/ supplies actual affine derived comparisons; DerivedHom/ supplies original open-cover
Hom and nilpotence results with the stated finite-cover/model/bound hypotheses. Plus/Additive
preserves the existing additivity declarations for the actual D-plus quotient.

Derived flat pullback has the original composition comparison, and scheme isomorphisms induce the original derived equivalences. The short-exact-sequence triangle retains its stated acyclicity assumptions.

These local general-theory candidates preserve the existing declaration namespaces, hypotheses and universes. Their K-theory applications remain in downstream modules.

- [`IsomorphismFunctors.lean`](IsomorphismFunctors.lean)
- [`PullbackComposition.lean`](PullbackComposition.lean)
- [`ShortExactTriangle.lean`](ShortExactTriangle.lean)

## Derived direct image, tensor, and projection formulas

`AlgebraicGeometry.Scheme.Modules.derivedPushforwardPlus f` is the installed right-derived
direct-image functor on D+. `derivedPushforwardPlusUnit f` compares actual
termwise direct image with it. The following proofs identify when that unit
is invertible, while retaining the original augmentations and units:

| Source module | Conditions and conclusion |
| --- | --- |
| [Aglib.AlgebraicGeometry.Cohomology.Affine.PushforwardAcyclicity](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Cohomology/Affine/PushforwardAcyclicity.lean), [`Pushforward/Affine`](Pushforward/Affine.lean) | Every quasicoherent sheaf is acyclic for an affine morphism; the unit on its degree-zero single is invertible |
| [`Pushforward/AffineBounded`](Pushforward/AffineBounded.lean) | Explicit lower and upper term bounds and degreewise quasicoherence give the same installed-unit comparison |
| [Aglib.AlgebraicGeometry.Cohomology.Flasque.Pushforward](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Cohomology/Flasque/Pushforward.lean), [`Pushforward/Flasque`](Pushforward/Flasque.lean), [native flasque derived-unit comparison](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Cohomology/Flasque/DerivedPushforward.lean) | For every scheme map, flasque sheaves are acyclic and the unit is invertible on bounded-below flasque-term complexes, with no upper bound |
| [Aglib.AlgebraicGeometry.Cohomology.Godement.First](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Cohomology/Godement/First.lean) | On every scheme and all module sheaves, the actual product of stalk skyscrapers is an exact flasque-valued functor with a natural monic germ unit |
| [Aglib.AlgebraicGeometry.Cohomology.Godement.Resolution](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Cohomology/Godement/Resolution.lean) | Actual natural augmented flasque sheaf resolution from the exact cokernel iteration, with the original germ augmentation quasi-isomorphism and preservation of short exact sequences |
| [Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Basic](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Cohomology/Godement/TotalComplex/Basic.lean), [Godement total exactness](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Cohomology/Godement/TotalComplex/Exactness.lean) | Actual natural totalization retains the lower bound and has flasque terms, preserving short exact sequences and degreewise monomorphisms |
| [Aglib.AlgebraicGeometry.Cohomology.Flasque.Extensions](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Cohomology/Flasque/Extensions.lean), [flasque direct-image exactness](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Cohomology/Flasque/PushforwardExactness.lean) | Actual flasque extension closure and direct-image short-exact preservation with flasque first terms; the complex direct-image statement requires no bound |
| [Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.QuasiIso](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Cohomology/Godement/TotalComplex/QuasiIso.lean), [Godement total direct-image comparison](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Cohomology/Godement/TotalComplex/Basic.lean) | Original total augmentation is a quasi-isomorphism for every Plus input; genuine weak maps are preserved, and Q(f_*T(K))≅Rf_*(Q(K)) is natural for every scheme map |
| [`Pushforward/FlatInjective`](Pushforward/FlatInjective.lean) | Flat direct image preserves injectives; the derived-Hom adjunction retains a bounded-below injective target complex |
| [`Pushforward/AffineComposite`](Pushforward/AffineComposite.lean) | The unit on `j_*M` is invertible when `j` and `j ≫ f` are affine and `M` is quasicoherent |

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
`godementResolution` constructs the natural cokernel C of that germ unit,
proves it exact by the actual snake diagram, and iterates it. The resolution
has terms G(C^n M) and the original quotient/unit differential. Its augmented
sequence is exact, its terms are flasque, and its natural augmentation from
M concentrated in degree zero is a quasi-isomorphism. The resolution preserves
short exact sequences and degreewise zero objects. `godementTotal`
totalizes the actual degreewise resolution bicomplex. An original total
degree is its finite diagonal biproduct for every lower-bounded input,
so the same lower bound and termwise flasqueness are retained.
[Godement total exactness](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Cohomology/Godement/TotalComplex/Exactness.lean) proves exactness using exact coproducts in the actual
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
live in [Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Basic](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/Algebra/Category/ModuleCat/Sheaf/Tensor/Basic.lean)
and `TensorExact`, with their site and universe hypotheses.
The [native tensor restriction](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Modules/Tensor/Restriction.lean) gives actual open restriction;
the [native finite locally free tensor exactness](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Modules/LocallyFree/Tensor/Exact.lean) proves short exactness for finite
locally free coefficients using affine finite-free retractions, including the
empty finite-free case. These constructions do not supply full monoidal coherence.

[Aglib.AlgebraicGeometry.Modules.Pushforward.Stalk](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Modules/Pushforward/Stalk.lean)
uses the actual pushforward germ map as a natural module-stalk isomorphism on
an inducing image and proves zero stalks off a closed image.
[Aglib.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Modules/Pushforward/ClosedImmersion.lean), [Aglib.AlgebraicGeometry.Modules.Stalk.Reflection](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Modules/Stalk/Reflection.lean)
therefore proves exact closed-immersion pushforward for arbitrary module sheaves,
without quasicoherence, finite generation or noetherian assumptions.
[Aglib.AlgebraicGeometry.Modules.Pushforward.SectionStalk](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Modules/Pushforward/SectionStalk.lean)
retains the original stalk ring retraction when the immersion is a section.

[Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Basic](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Modules/Tensor/Stalk/Basic.lean)
identifies the literal sheaf tensor stalk with the tensor of the two module
stalks, using the original pure-section germs in both directions.
[Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Naturality](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Modules/Tensor/Stalk/Naturality.lean)
preserves both original sheaf-variable maps. Neither coefficient requires
flatness or quasicoherence.

The [native finite locally free projection formula](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Modules/ProjectionFormula/FiniteLocallyFree.lean) proves the ordinary projection formula
for every scheme map, arbitrary source module sheaf, and finite locally free
target coefficient. `projectionFormulaIso` has the original geometric
adjunction-unit composite as its forward arrow. The [derived projection formula](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Cohomology/ProjectionFormula/Basic.lean)
gives its bounded-below derived natural isomorphism, with both-variable
naturality and the installed-unit equations; there is no upper bound or extra
global flasqueness hypothesis.

For a closed immersion and arbitrary coefficient/source module sheaves,
[Aglib.AlgebraicGeometry.Modules.ProjectionFormula.ClosedImmersion](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Modules/ProjectionFormula/ClosedImmersion.lean), [Aglib.AlgebraicGeometry.Modules.Stalk.Reflection](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Modules/Stalk/Reflection.lean)
proves the original `projectionFormulaMap` invertible, with both-variable
naturality. [Pullback stalk units](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Modules/Pullback/StalkUnit.lean) and [projection-formula stalks](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Modules/ProjectionFormula/Stalk.lean) retain its actual
adjunction-unit germ and scalar-extension tensor formula on image stalks;
both stalk objects vanish off the image. No coefficient flatness,
quasicoherence or noetherian assumption is added. This ordinary comparison
does not assert a general D+ tensor projection formula.

## Native affine and derived compatibility

Pinned Aglib `52e09db47998f139064acf48a2d3a64494d0dd9a` supplies the original affine injective resolution, derived flat pullback composition, and commuting-square comparison directly. Their copied implementations are retired. Quillen retains its additional Ext, inverse-unit, and ordered unit-square theorems.

For the same commuting-square comparison, the native arguments are `(c, a, b, j, h.symm)` in place of the former `(a, j, c, b, h)`. This order and reversed equality preserve the direction and actual comparison map. The native quasicoherent extension instance and `unitMul_zero` likewise supply the shared interfaces directly.
