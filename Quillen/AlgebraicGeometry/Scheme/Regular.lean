/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Regular.SmallComparison
public import Quillen.AlgebraicGeometry.Scheme.Regular.Field
public import Quillen.AlgebraicGeometry.Scheme.Regular.AffineLowDimension
public import Quillen.AlgebraicGeometry.Scheme.Regular.AffineFiniteDimension
public import Quillen.AlgebraicGeometry.Scheme.Regular.Affine
public import Quillen.AlgebraicGeometry.Scheme.Regular.GlobalComparison

/-!
# Checked canonical regular K-to-G equivalences

`Scheme.KToGRegularAffineEquiv` proves the original canonical K-to-G comparison
for every regular affine ring, with no finite Krull-dimension bound. PID,
field and finite-dimensional specializations remain available. Every forward
homomorphism is exactly the existing `Scheme.KToG`.
`Scheme.KToGRegularEquiv` also proves the canonical comparison for every
quasi-compact regular scheme with the ordinary resolution property. Its
finite resolutions are derived, without a global dimension bound.
-/
@[expose] public section
