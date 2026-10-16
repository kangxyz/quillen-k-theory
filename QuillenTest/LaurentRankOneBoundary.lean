/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LaurentRankOneBoundary
public import Mathlib.Data.ZMod.Basic

/-! Original forward and inverse Laurent units retain opposite terminal rank-one classes. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.LaurentRankOneBoundary

/-- The original forward rank-one terminal boundary cancels the original rank-one object class.
-/
theorem forward_terminal_rankOne_cancel (R : CommRingCat.{u}) :
    positiveBassBoundary R 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
          (rankOnePerfect (Spec (.of (LaurentPolynomial R))))) *
      (perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R)) = 1 := by
  rw [positiveBassBoundary_forward_rankOne]
  exact inv_mul_cancel _

/-- Inverting the actual Laurent unit gives the positive original rank-one class. -/
theorem inverse_terminal_rankOne (R : CommRingCat.{u}) :
    positiveBassBoundary R 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)⁻¹
          (rankOnePerfect (Spec (.of (LaurentPolynomial R))))) =
      (perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R)) := by
  rw [perfectGlobalUnitKOneClass_inv, map_inv, positiveBassBoundary_forward_rankOne, inv_inv]

/-- The literal original boundary formula also includes the zero ring. -/
theorem zero_ring_terminal_rankOne :
    positiveBassBoundary (.of (ZMod 1)) 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit (.of (ZMod 1)))
          (rankOnePerfect (Spec (.of (LaurentPolynomial (ZMod 1)))))) =
      ((perfectWaldhausen (Spec (.of (ZMod 1)))).kZeroObjectClass
        (rankOnePerfect (Spec (.of (ZMod 1)))))⁻¹ :=
  positiveBassBoundary_forward_rankOne _

end QuillenTest.LaurentRankOneBoundary
