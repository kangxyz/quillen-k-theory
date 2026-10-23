# Derived base-change mates

## Local candidate interfaces

The original derived flat base-change map is compatible with horizontal and vertical pasting, shifts, isomorphic coordinates, and open localization. Affine and two-open results keep their quasicoherent, flatness, boundedness and cover assumptions; no additional general base-change assertion is introduced.

These local general-theory candidates preserve the existing declaration namespaces, hypotheses and universes. Their K-theory applications remain in downstream modules.

Shift compatibility uses the [native Aglib owner](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/AlgebraicGeometry/Cohomology/BaseChange/Derived/Shift.lean) for the original flat pullback and base-change mate.

- [`Affine.lean`](Affine.lean)
- [`AffineComposite.lean`](AffineComposite.lean)
- [`AffineCoordinates.lean`](AffineCoordinates.lean)
- [`AffineLocal.lean`](AffineLocal.lean)
- [`BaseOpen.lean`](BaseOpen.lean)
- [`Coordinates.lean`](Coordinates.lean)
- [`Horizontal.lean`](Horizontal.lean)
- [`Localization.lean`](Localization.lean)
- [`OpenCover.lean`](OpenCover.lean)
- [`OpenImmersion.lean`](OpenImmersion.lean)
- [`OpenRestriction.lean`](OpenRestriction.lean)
- [`TwoOpen.lean`](TwoOpen.lean)
- [`Vertical.lean`](Vertical.lean)

## Canonical base-change mates

On a genuine cartesian square, the [native cartesian base-change module](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/AlgebraicGeometry/Modules/BaseChange/Cartesian.lean) constructs
the geometric mate from pullback/direct-image adjunctions.
The native affine base-change modules and local [`ScalarSquare`](../Affine/ScalarSquare.lean) and [`QuasiCoherent`](../Affine/QuasiCoherent.lean) leaves identify
it with the extension/restriction-of-scalars mate on spectra. It is invertible
on every quasicoherent sheaf in an affine cartesian square, without flatness
or finite-generation assumptions, retaining the original tensor and unit formulas.
[`Pasting`](../Cartesian/Pasting.lean), [`Horizontal`](../Cartesian/Horizontal.lean), and
[`Localization`](../Cartesian/Localization.lean) give vertical/horizontal equations and
open-cover detection with their local invertibility premises explicit.

`derivedFlatBaseChangeMap` is constructed from that same ordinary mate, with
a flat base leg and an actual cartesian square. Flatness of the pulled-back
leg follows from the square; exact pullback preserves homology without an
injective-preservation assumption. Its defining equation keeps both installed
composite units. The scope of invertibility is:

| Source module | Invertibility proved |
| --- | --- |
| [`OpenRestriction`](OpenRestriction.lean), [`Cartesian/OpenImmersion`](../Cartesian/OpenImmersion.lean), [native derived open base change](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/AlgebraicGeometry/Cohomology/BaseChange/Derived/Restriction.lean) | Every bounded-below complex for an open base leg and arbitrary scheme map; the installed open comparison is the same canonical mate |
| [`Affine`](Affine.lean), [`AffineCoordinates`](AffineCoordinates.lean), [`AffineLocal`](AffineLocal.lean) | Quasicoherent singles and their integer shifts for affine morphisms and flat base change, including nonaffine ambient schemes |

The native shift interface and local [`Horizontal`](Horizontal.lean),
[`Vertical`](Vertical.lean), and [`Localization`](Localization.lean) leaves retain
shift, pasting, and target-open equations. [`OpenCover`](OpenCover.lean) gives
cover conservativity. [`AffineComposite`](AffineComposite.lean) and
[`TwoOpen`](TwoOpen.lean) transport the mate through actual chart images and
the signed two-open triangle.

The pinned native [derived locality theorem](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/AlgebraicGeometry/Cohomology/BaseChange/Derived/Locality.lean)
additionally proves `derivedFlatBaseChangeMap_isIso_of_quasicoherent_homology`:
for an actual cartesian square, flat base leg and quasi-compact quasi-separated
direct-image map, the same mate is invertible on every D+ object whose original
homology sheaves are quasicoherent. Import
`Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Locality` for this endpoint; the local bridge leaves listed above do not themselves
import this native locality leaf. It requires no termwise quasicoherence, upper bound, Noetherianity or finite
generation; it does not assert invertibility for arbitrary non-quasicoherent
coefficients or unrestricted direct-image maps.

## Native shift interface

Derived flat base-change shift compatibility uses the native Aglib leaf `Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Shift` directly. The copied `Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.Derived.Shift` implementation is retired. The original functor shift data and dependent compatibility proposition are retained; no additional shift or base-change premise is introduced.
