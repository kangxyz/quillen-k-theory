/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Finite affine covers

A quasi-compact scheme has a finite affine subcover retaining the original chart rings and
open-immersion maps.-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- A finite affine subcover of a quasi-compact scheme, retaining the
actual chart rings and open-immersion maps from the chosen affine cover. -/
def finiteAffineOpenCover (X : AlgebraicGeometry.Scheme.{u}) [CompactSpace X] :
    X.AffineOpenCover where
  I₀ := X.affineCover.finiteSubcover.I₀
  X i := X.affineOpenCover.X (X.affineCover.idx i.1)
  f := X.affineCover.finiteSubcover.f
  idx := X.affineCover.finiteSubcover.idx
  covers := X.affineCover.finiteSubcover.covers
  map_prop := X.affineCover.finiteSubcover.map_prop

instance instFintypeFiniteAffineOpenCover (X : AlgebraicGeometry.Scheme.{u}) [CompactSpace X] :
    Fintype (finiteAffineOpenCover X).I₀ := by
  change Fintype X.affineCover.finiteSubcover.I₀
  infer_instance

end AlgebraicGeometry.Scheme
