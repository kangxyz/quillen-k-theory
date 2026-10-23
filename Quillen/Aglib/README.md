# Aglib candidate interfaces

`Quillen.Aglib` is the current import prefix for local general-theory candidates;
declaration namespaces describe the native mathematical objects. Native
extractions use the mathematical namespaces documented in the family guides;
local extensions preserve their stated objects, hypotheses and chosen comparison
maps. The prefix records local ownership and does not assert upstream admission.
Q/K/G/S, Waldhausen,
spectra and specialized projective-line constructions retain their application owners.

Native imports use the mathematical Aglib revision
`2c34f185fa859e862661f939cd216b07bcccfb26` pinned in
[`lake-manifest.json`](../../lake-manifest.json). Focused `Aglib.*` imports own
interfaces already supplied there; local `Quillen.Aglib.*` leaves retain the
additional candidates described below.

Candidate authoring follows the
[development policy](../../docs/DEVELOPMENT.md#aglib-candidates).

## Mathematical interfaces and results

| Family | Interfaces and main results |
| --- | --- |
| [Module constructions](Algebra/Module/README.md) | Finite-projective retracts, finite defect parametrices, matrix presentations and balanced scalar extension |
| [Module complexes](Algebra/Homology/ModuleCat/README.md) | Ordinary complex, tensor, exactness and homology interfaces |
| [Integral bar homology](RepresentationTheory/Homological/GroupHomology/README.md) | Original low-degree bar cocycles, perfect central extensions, integer coefficient restriction and marked torus cycles |
| [Endofunctor words](CategoryTheory/Endofunctor/README.md) | Specified finite words from a natural square automorphism, with explicit association and recursive component formulas |
| [Exact-category filtrations](CategoryTheory/ExactCategory/Filtration/README.md) | Actual filtrations, factors and additive-invariant formulas under their conflation hypotheses |
| [Displayed colimits](CategoryTheory/Limits/README.md) | Lower-ideal gluing and pointwise pushout interchange |
| [Fibers and cocartesian sections](CategoryTheory/FiberedCategory/README.md) | Literal change of index, evaluation, reindexing and preservation of one chosen-zero family |
| [Paths and homotopies](Topology/Path/README.md) | Whole path reconstruction, pointwise evaluation and exact homotopy pasting for coefficient Bass carriers |
| [Regular-local algebra](RingTheory/RegularLocalRing/README.md) | Local algebra and finite projective-dimension bounds with the original hypotheses |
| [Scheme module sheaves](AlgebraicGeometry/Modules/README.md) | Coherent/quasicoherent operations, ordinary and derived complexes, and intrinsic perfect-complex theory |
| [Scheme products](AlgebraicGeometry/Products/README.md) | Independent-factor swaps, their braid equation, scalar pullback, external-factor transport and integral coefficient/product row isomorphisms |
| [Polynomial/Laurent spectra](AlgebraicGeometry/Spec/PolynomialLaurent/README.md) | Canonical affine schemes, ring maps, coordinates, base-change squares, open immersions, the arbitrary-scheme index square and its integral Spec-row/unit comparisons |

Public import entry: `Quillen.Aglib`. Prefer the focused leaves described in the
family guides for implementation dependencies. The 0.10.0 native namespace
migrations are recorded in
[compatibility notes](../../docs/COMPATIBILITY.md#native-aglib-adoption-in-0100);
original Q/K/G/S, Waldhausen, spectrum and specialized
curve/projective-line constructions remain in their application owners.

Current affine/derived interfaces are in the
[derived-category guide](AlgebraicGeometry/Modules/DerivedCategory/README.md),
[derived base change](AlgebraicGeometry/Modules/BaseChange/Derived/README.md),
[coherent/finite-type interfaces](../AlgebraicGeometry/Scheme/Coherent/README.md),
and [scalar base change](Algebra/Category/ModuleCat/README.md).

## Extensions of native leaves

Nineteen extracted implementations now use precise native `Aglib.*` leaves;
their retired `Quillen.Aglib.*` imports have no compatibility facade. The
[compatibility mapping](../../docs/COMPATIBILITY.md#native-aglib-adoption-in-0100)
lists every replacement. Eight same-path local leaves retain additional APIs:

| Local leaf | Retained interface |
| --- | --- |
| `CategoryTheory/Pi/Abelian` | `CategoryTheory.Pi.shortExact_pi_iff` and `exactEvaluation`, extending [`Aglib.CategoryTheory.Pi.Abelian`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/CategoryTheory/Pi/Abelian.lean) |
| `CategoryTheory/Pi/FiniteSupport` | Exact-structure abbreviation, exact inclusion and evaluation object/map simp lemmas, extending [`Aglib.CategoryTheory.Pi.FiniteSupport`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/CategoryTheory/Pi/FiniteSupport.lean); the native leaf supplies evaluation and its Abelian instance |
| `Algebra/Homology/CochainComplexPlus/Shift` | `CochainComplex.Plus.quasiIsoCompatibleWithShift`, extending [`Aglib.Algebra.Homology.CochainComplexPlus.Shift`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Homology/CochainComplexPlus/Shift.lean) |
| `Algebra/Category/FGModuleCat/ScalarMatrices` | Commutative-ring `matrixToAut` and application formula, using native `linearAutToFGAut` from [`Aglib.Algebra.Category.FGModuleCat.ScalarMatrices`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Category/FGModuleCat/ScalarMatrices.lean) |
| `AlgebraicGeometry/Spec/PolynomialLaurent/ZeroSection` | Arbitrary-scheme Bass zero-section constructions, using native affine `polynomialZeroSection` from [`Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.ZeroSection`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/ZeroSection.lean) |
| `RingTheory/RegularLocalRing/ProjectiveDimension` | Existing `Quillen.RegularLocal` finite-module projective-dimension bounds and resolution proof |
| `AlgebraicGeometry/Modules/PerfectComplexes/Restriction` | Existing locally-perfect restriction and exactness APIs; native strict-perfect restriction has a different scope |
| `CategoryTheory/Limits/Shapes/CokernelPushout` | Existing `HasZeroMorphisms` cokernel-pushout theorem; native theorem assumes preadditivity |
