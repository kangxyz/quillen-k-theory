/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarSupportedBoundary
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Coordinates
public import Mathlib.Data.ZMod.Basic

/-! The original forward Laurent rank-one class has the inverse negative local cone boundary. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.ScalarSupportedBoundary

/-- This is the literal negative-chart localization boundary into its actual supported group. -/
theorem forward_laurent_negative_boundary (R : CommRingCat.{u}) :
    qcqsPerfectConnectingHom (laurentMinus R) 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
          (rankOnePerfect (Spec (.of (LaurentPolynomial R))))) =
      ((perfectSupportedWaldhausen (laurentMinus R)).kZeroObjectClass
        ((perfectAcyclicToSupported (laurentMinus R)).obj
          (perfectOpenScalarCone (laurentMinus R) (polynomialGlobalCoordinate R)
            (laurentGlobalUnit R)⁻¹ (polynomialGlobalCoordinate_laurentMinus R)
            (rankOnePerfect (Spec (.of (Polynomial R)))))))⁻¹ := by
  have h := qcqsPerfectConnectingHom_globalUnit_rankOne (laurentMinus R)
    (polynomialGlobalCoordinate R) (laurentGlobalUnit R)⁻¹
    (polynomialGlobalCoordinate_laurentMinus R)
  rw [perfectGlobalUnitKOneClass_inv, map_inv] at h
  simpa only [inv_inv] using congrArg Inv.inv h

/-- The actual supported negative-chart statement includes the zero ring. -/
private theorem zero_ring_forward_laurent_negative_boundary :
    qcqsPerfectConnectingHom (laurentMinus (.of (ZMod 1))) 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit (.of (ZMod 1)))
          (rankOnePerfect (Spec (.of (LaurentPolynomial (ZMod 1)))))) =
      ((perfectSupportedWaldhausen (laurentMinus (.of (ZMod 1)))).kZeroObjectClass
        ((perfectAcyclicToSupported (laurentMinus (.of (ZMod 1)))).obj
          (perfectOpenScalarCone (laurentMinus (.of (ZMod 1)))
            (polynomialGlobalCoordinate (.of (ZMod 1))) (laurentGlobalUnit (.of (ZMod 1)))⁻¹
            (polynomialGlobalCoordinate_laurentMinus (.of (ZMod 1)))
            (rankOnePerfect (Spec (.of (Polynomial (ZMod 1))))))))⁻¹ :=
  forward_laurent_negative_boundary _

end QuillenTest.ScalarSupportedBoundary
