# Original field K1 and K2 comparisons

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.KTheory.Field.SteinbergFiberComparison` | Actual plus-map fiber central extension, Steinberg lift and kernel-to-original-finite-projective-right-module-K2 map; no comparison isomorphism or positive product marking is asserted |
| `Quillen.KTheory.Field.SteinbergFiberNaturality` | Original projective-right K2 comparison commutes with actual field extension, preserving the original Steinberg map and correction paths |
| `Quillen.KTheory.Field.SteinbergFiberSurjectivity` | Original lift/kernel/pi2/projective-K2 maps are surjective under actual fiber perfectness, now supplied by `Plus.StableFiberPerfectness` |
| `Quillen.KTheory.Field.MilnorKTwoComparison` | Canonical ordered-symbol Milnor maps to original right-projective K2 and, by explicit equivalence, upper finite-module K2; original field-extension squares; conditional surjectivity and finite-field triviality retain actual fiber perfectness |
| `Quillen.KTheory.Field.MilnorKTwoSurjectivity` | Discharges the stage-containment input by actual all-rank kernel generation; four surjectivity/finite-field wrappers retain only actual stable-fiber perfectness and the stated field/finiteness assumptions |
| `Quillen.KTheory.Field.FiniteFieldKTwo` | Unconditional subsingleton and `eq_one` over every finite field for original right-projective K2, actual upper/lower finite-module K2/G2 and literal public coherent G2(Spec F) |
| `Quillen.KTheory.Field.ProjectiveDeterminant` | Original projective-Q K1 determinant and actual base-change square |
| `Quillen.KTheory.Field.ModuleDeterminant` | Upper finite-module K1 determinant with literal tensor-extension naturality |
| `Quillen.KTheory.Field.MatrixCubeComparison` | `moduleDetEquiv_matrix_cube` on the literal upper-small positive matrix cube, every field and rank including zero |
| `Quillen.KTheory.Field.MatrixTransport` | Original free-module coordinate isomorphism to the standard action of the same matrix |

## Stable determinant and the original projective comparison

Import
[`Quillen.Algebra.Group.StableFieldDeterminant`](../../Algebra/Group/StableFieldDeterminant.lean).
In `Quillen.StableGeneralLinear`, `det` is defined on the actual stable matrix
group over every commutative ring. Over every field, `ker_det` identifies its
kernel with the actual stable elementary subgroup, and `quotientDetEquiv`
identifies the actual elementary quotient with field units. Finite matrix
values and the literal ring-change square are proved. Rank zero and small
finite fields have no exceptional hypotheses.

[`ElementaryProjectiveKOne`](ElementaryProjectiveKOne.lean)
composes the original elementary-quotient/completion and positive Q
comparisons. Its ring-change theorem retains the specified basepoint tracks.
[`ProjectiveDeterminant`](ProjectiveDeterminant.lean)
defines `StableCompletion.projectiveDetEquiv` by the inverse of that composite.
Its matrix equation uses the original stable-completion representative, and
its scalar-extension square uses `rightBaseChangeExact`.

The finite-projective/finite-module and explicit opposite-ring comparisons
are in `ProjectiveFiniteModules` and `FiniteModuleRingEquivalence`.
`ScalarExtensionComparison` compares native right base change with literal
finite-module tensor extension, including the actual upper SmallModel K-map
square. These transports preserve the original objects and functors.

[`ModuleDeterminant`](ModuleDeterminant.lean)
defines `Quillen.Field.moduleDetEquiv` on the actual
`(finiteModuleExactStructure F).SmallK.{u+1} 1`, with literal tensor-extension
naturality and determinant on the transported native completion representative.
[`MatrixCubeComparison`](MatrixCubeComparison.lean)
proves `Quillen.Field.moduleDetEquiv_matrix_cube`: this same determinant
sends the literal `Automorphism.Cube.automorphismFirstCube` of the original
upper-small matrix automorphism to `Matrix.GeneralLinearGroup.det g`.
The theorem covers every field and every rank, including zero. The proof
uses the actual finite-stage localized homotopy, standard-matrix coordinate
transport, and inverse-first/right-cap normalization. It does not require
a global completion-to-positive H-map.

## Native Milnor symbols

[`FiniteFieldKTwo`](FiniteFieldKTwo.lean) proves the
unconditional finite-field consequence. For every `[Field F] [Finite F]`,
the original right-projective K2, actual upper finite-module K2, original lower
finite-module G2 and literal public coherent G2 of `Spec F` have one element.
The lower/public transports are the canonical universe and affine G comparisons.
F2/F3/F5 and general finite-field consumers are checked. This theorem needs
neither Matsumoto injectivity nor positive product marking.

[`FiniteResidueLocalization`](../../GTheory/Dedekind/FiniteResidueLocalization.lean)
then proves original native/public generic G2 injectivity over a Dedekind domain
whose actual height-one residue fields are finite. Its public pullback retains
the algebra map to a supplied fraction field. Integer and Spec Q to Spec Z
consumers use actual finite quotients; generic G1 injectivity is separate.

## Original Steinberg and positive-product maps

[`StableSteinbergUniversal`](../../Algebra/Group/StableSteinbergUniversal.lean)
proves unique lifting into an arbitrary surjective central extension of the
original elementary group. The actual ordered torus defect in
[`StableSteinbergSymbols`](../../Algebra/Group/StableSteinbergSymbols.lean)
is bilinear and Steinberg, yielding `milnorToKernel` directly from Aglib's
supplied interfaces with its original field-map square.
[`SteinbergFiberComparison`](SteinbergFiberComparison.lean)
constructs the actual plus-map fiber central extension and the resulting
map from the Steinberg kernel to original finite-projective right-module K2.
Finite-module transport must be a subsequent explicit composition.
[`SteinbergFiberNaturality`](SteinbergFiberNaturality.lean)
proves the exact original field-extension square.
[`SteinbergFiberSurjectivity`](SteinbergFiberSurjectivity.lean)
proves surjectivity under actual fiber perfectness. The later
[`StableFiberPerfectness`](../Plus/StableFiberPerfectness.lean)
supplies that input as a proved theorem on the existing field-fiber alias.
[`StableSteinbergRankTwo`](../../Algebra/Group/StableSteinbergRankTwo.lean)
identifies the defect subgroup with the original rank-two kernel.
[`StableSteinbergKernelGeneration`](../../Algebra/Group/StableSteinbergKernelGeneration.lean)
now proves all-rank descent, equality with the full original kernel and
surjectivity of the unchanged ordered-symbol Milnor map. Its actual parabolic
and `B V B` source-word proof includes zero pivots and fields of orders two
and three; it assumes no unstable Steinberg-stage injectivity.
[`MilnorKTwoComparison`](MilnorKTwoComparison.lean)
composes this existing Milnor map with the original right-projective K2
comparison and then explicitly with the upper finite-module equivalence.
Both endpoints retain their original field-extension squares and literal
ordered-defect values.
[`MilnorKTwoSurjectivity`](MilnorKTwoSurjectivity.lean)
discharges the stage-containment input. The proved fiber perfectness then gives
surjectivity onto these Quillen groups. The original Milnor map is now injective for fields of characteristic zero; see the characteristic-zero equivalences below.
[`SteinbergFiberInjectivity`](SteinbergFiberInjectivity.lean)
proves injectivity of the original kernel-to-right-projective K2 map and
bijectivity of the original Steinberg-to-stable-fiber map over every field.
Its geometric/Schur construction retains the original basepoint paths, cover
maps and signed torus generators. It is independent of Milnor-map injectivity.
The [original transgression](SteinbergFiberTransgression.lean) and
[commuting-square capping](../../Topology/HomotopyFiber/CommutingSquareCapping.lean)
use the oriented square cycle given by the lower triangle `00,10,11` minus the
upper triangle `00,01,11`. Their marked comparison retains the signs

```text
original Steinberg defect -> inverse transported sphere class
                         -> negative oriented square class
                         -> negative integral bar torus
                         = original algebraic Schur marking.
```

All-rank defect generation extends the pair marking to the whole original
kernel. This route requires neither simple connectedness of the original
source nor a full Hurewicz isomorphism. The finite faithful-coefficient argument
for Milnor injectivity is a separate construction.
[`PositiveSymbolMarking`](PositiveSymbolMarking.lean)
proves `Field.milnorToUpperModuleKTwo_pair_eq_unitProduct` for every field.
It identifies the same original Milnor map on ordered pairs with the positive
scalar-operation product, retaining the forward opposite-unit action and
original projective-to-module comparison.

The original positive marking holds over every field, with the literal equation:

```lean
Field.milnorToUpperModuleKTwo F (MilnorK.symbol ![a, b]) =
  Additive.ofMul (FieldSymbols.unitProduct F a b)
```

## Characteristic-zero original Milnor equivalences

Import [MilnorKTwoEquivalence](MilnorKTwoEquivalence.lean). For `F : Type u`
with `[Field F] [CharZero F]`,
`Quillen.Field.milnorRightProjectiveKTwoEquivCharZero` and
`milnorUpperModuleKTwoEquivCharZero` are additive equivalences from the existing
`MilnorK.K F 2` to additive original right-projective K2 and upper finite-module
K2. Their forward homomorphisms are exactly the existing
`milnorToRightProjectiveKTwo` and `milnorToUpperModuleKTwo`.
The [Matsumoto construction](../../Algebra/Group/StableSteinberg/Matsumoto/README.md)
proves injectivity into the original Steinberg kernel. Combining it with the
all-field kernel-to-Quillen comparison above gives these equivalences.
No additional detector, generation, fiber-perfectness or product-marking
premise is required: the native constructions supply these inputs.

The original ordered symbol maps to the actual positive scalar unit product.
Forward and inverse equivalences commute with the original field-extension
maps for characteristic-zero fields in the same universe; the right-projective
map uses original right scalar extension and the upper map uses literal tensor
extension. These are the exact existing maps, not an unspecified isomorphism.

`upperModuleKTwoMilnorNegativeEquivCharZero` is **minus the inverse** of the
positive upper equivalence. It sends the original positive ordered product
to `-MilnorK.symbol ![a,b]`. Its inverse is minus the same original forward
Milnor map. Both directions retain the original field-map squares. Canonical
promotion/lowering gives the same normalization in the
[lower model](../LowDegreeScalarAction/README.md#same-negative-inverse-and-dvr-boundaries).

## Current boundary

The original Milnor-to-Steinberg injectivity and original right/upper Quillen
equivalences are native theorems for `Field` plus `CharZero`. All-field finite
Bruhat extensions, original Steinberg/fiber comparison and positive pair marking
retain their own broader scopes. Unconditional finite-field K2/G2 vanishing
includes F2 and F3 and does not require a characteristic-zero equivalence.
No injectivity/equivalence for infinite positive-characteristic fields is claimed.
An arbitrary-DVR local Milnor presentation and broad R5 background integration
are separate, unclaimed endpoints.

## Classical reference locators

[Weibel, The K-book, chapter III](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.III.pdf):
1.1.1--1.2.2 for determinant and field elimination, 5.4--5.5 for universal
central extensions, 5.10.1--5.10.2 for the literal torus words and Steinberg
word calculation, 5.10.5 for kernel symbol generation, 6.1 for the full symbol
presentation, and 6.1.1 for finite fields. These chapter-III algebraic locators are distinct from the native original-topological-group comparisons described above.

[Chapter IV](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.IV.pdf):
1.7.1 for the classical degree-two comparison, 6.4 for product/filtered-union
behavior, and Exercise 7.9 for the automorphism representative. These locate
the mathematics; they do not discharge the native constructions above.

## Current original-map client

[Consumer.MilnorKTwoEquivalence](../../../examples/downstream/Consumer/MilnorKTwoEquivalence.lean)
checks original base-change and inverse-sign equations and the actual
`ℚ → RatFunc ℚ` scalar cube. Right-projective modules use `Fᵐᵒᵖ`; the subsequent
upper/lower transports are the explicit canonical comparisons above.
