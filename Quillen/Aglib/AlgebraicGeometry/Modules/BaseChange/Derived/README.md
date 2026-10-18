# Derived base-change mates

## Local candidate interfaces

The original derived flat base-change map is compatible with horizontal and vertical pasting, shifts, isomorphic coordinates, and open localization. Affine and two-open results keep their quasicoherent, flatness, boundedness and cover assumptions; no additional general base-change assertion is introduced.

These local general-theory candidates preserve the existing declaration namespaces, hypotheses and universes. Their K-theory applications remain in downstream modules.

Shift compatibility uses the [native Aglib owner](https://github.com/kangxyz/aglib/blob/5895002fb55a4b371fdbd34f18e06c49d8c2dc7a/Aglib/AlgebraicGeometry/Cohomology/BaseChange/Derived/Shift.lean) for the original flat pullback and base-change mate.

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
| [`DerivedOpenBaseChange`](OpenRestriction.lean), `CartesianOpenBaseChangeMate`, `DerivedFlatBaseChangeOpen` | Every bounded-below complex for an open base leg and arbitrary scheme map; the installed open comparison is the same canonical mate |
| [`AffineDerivedBaseChange`](Affine.lean), `AffineDerivedBaseChangeCoordinates`, `AffineDerivedBaseChangeLocal` | Quasicoherent singles and their integer shifts for affine morphisms and flat base change, including nonaffine ambient schemes |

`DerivedFlatBaseChangeShift`, `DerivedFlatBaseChangeHorizontal`,
`DerivedFlatBaseChangeVertical`, and `DerivedFlatBaseChangeLocalization` retain
shift, pasting, and target-open equations. `DerivedOpenCoverConservativity` and
`DerivedFlatBaseChangeOpenCover` give cover conservativity.
`AffineCompositeDerivedBaseChange` and `TwoOpenDerivedBaseChange` transport the
mate through actual chart images and the signed two-open triangle. General
bounded-below flat-base-change invertibility is not inferred from the single-sheaf
results.

## Native shift interface

Derived flat base-change shift compatibility uses the native Aglib leaf `Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Shift` directly. The copied `Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.Derived.Shift` implementation is retired. The original functor shift data and dependent compatibility proposition are retained; no additional shift or base-change premise is introduced.
