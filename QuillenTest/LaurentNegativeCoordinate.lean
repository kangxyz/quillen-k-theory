/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Coordinates
public import Mathlib.Data.ZMod.Basic

/-! The two original chart coordinates multiply to one on their actual Laurent overlap. -/
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option warningAsError true

@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.LaurentNegativeCoordinate

/-- Both original chart restriction maps retain their opposite coordinate orientations. -/
theorem original_chart_coordinates_mul (R : CommRingCat.{u}) :
    (laurentPlus R).appTop (polynomialGlobalCoordinate R) *
      (laurentMinus R).appTop (polynomialGlobalCoordinate R) = 1 := by
  rw [polynomialGlobalCoordinate_laurentPlus, polynomialGlobalCoordinate_laurentMinus]
  exact Units.mul_inv (laurentGlobalUnit R)

/-- The chart compatibility also applies to the empty affine spectrum of the zero ring. -/
private theorem zero_ring_chart_coordinates_mul :
    (laurentPlus (.of (ZMod 1))).appTop (polynomialGlobalCoordinate (.of (ZMod 1))) *
      (laurentMinus (.of (ZMod 1))).appTop (polynomialGlobalCoordinate (.of (ZMod 1))) = 1 :=
  original_chart_coordinates_mul _

end QuillenTest.LaurentNegativeCoordinate
