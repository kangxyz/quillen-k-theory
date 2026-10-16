/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LaurentOverlapScalarBoundary
public import QuillenTest.NativeAffineBase
public import QuillenTest.RestrictionIsoEquivalence
public import Mathlib.Data.ZMod.Basic

/-! The actual overlap boundary cancels its original negative scalar cone, including over zero. -/
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
namespace QuillenTest.LaurentOverlapScalarBoundary

/-- The original lower boundary and actual scalar-cone class cancel on the unchanged overlap. -/
theorem overlap_boundary_cone_cancel (R : CommRingCat.{u}) :
    qcqsPerfectConnectingHom (overlapOpen R).ι 0
        ((laurentOverlapEquiv R 1).symm
          (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
            (rankOnePerfect (Spec (.of (LaurentPolynomial R)))))) *
      (perfectSupportedWaldhausen (overlapOpen R).ι).kZeroObjectClass
        ((perfectAcyclicToSupported (overlapOpen R).ι).obj
          (perfectOpenScalarCone (overlapOpen R).ι (polynomialGlobalCoordinate R)
            (overlapLaurentGlobalUnit R)⁻¹ (polynomialGlobalCoordinate_overlap R)
            (rankOnePerfect (Spec (.of (Polynomial R)))))) = 1 := by
  rw [laurentOverlap_forward_rankOne_boundary]
  exact inv_mul_cancel _

/-- The actual overlap restriction, not a chosen Laurent identification, also covers zero rings. -/
theorem zero_ring_overlap_unit :
    (laurentOverlapEquiv (.of (ZMod 1)) 1).symm
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit (.of (ZMod 1)))
          (rankOnePerfect (Spec (.of (LaurentPolynomial (ZMod 1)))))) =
      perfectGlobalUnitKOneClass _ (overlapLaurentGlobalUnit (.of (ZMod 1)))
        (rankOnePerfect (overlapOpen (.of (ZMod 1))).toScheme) :=
  laurentOverlapEquiv_symm_globalUnit_rankOne _

end QuillenTest.LaurentOverlapScalarBoundary
