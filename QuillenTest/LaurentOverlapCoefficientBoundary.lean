/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LaurentOverlapCoefficientBoundary
public import Mathlib.Data.ZMod.Basic

public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
/-! Exact overlap composition and signed boundary with arbitrary polynomial coefficients. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.LaurentOverlapCoefficientBoundary

/-- The actual comparison contains the original restriction composition and original equality. -/
theorem original_overlap_composition (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :
    (laurentOverlapCoefficientIso R K).hom.hom =
      (restrictCompIso (overlapOpenIso R).inv (laurentMinus R)).hom.app K.obj ≫
        (eqToIso (restrict_congr (overlapOpenIso_inv_laurentMinus R))).hom.app K.obj := rfl

/-- The unchanged boundary cancels the literal scalar cone on the same coefficient. -/
theorem coefficient_overlap_boundary_cancel (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :
    qcqsPerfectConnectingHom (overlapOpen R).ι 0
        ((laurentOverlapEquiv R 1).symm
          (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
            ((perfectRestrict (laurentMinus R)).obj K))) *
      (perfectSupportedWaldhausen (overlapOpen R).ι).kZeroObjectClass
        ((perfectAcyclicToSupported (overlapOpen R).ι).obj
          (perfectOpenScalarCone (overlapOpen R).ι (polynomialGlobalCoordinate R)
            (overlapLaurentGlobalUnit R)⁻¹ (polynomialGlobalCoordinate_overlap R) K)) = 1 := by
  rw [laurentOverlap_forward_coefficient_boundary]
  exact inv_mul_cancel _

/-- Actual coefficient transport also retains the zero ring. -/
theorem zero_ring_overlap_coefficient
    (K : Perfect (Spec (.of (Polynomial (ZMod 1))))) :
    (laurentOverlapEquiv (.of (ZMod 1)) 1).symm
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit (.of (ZMod 1)))
          ((perfectRestrict (laurentMinus (.of (ZMod 1)))).obj K)) =
      perfectGlobalUnitKOneClass _ (overlapLaurentGlobalUnit (.of (ZMod 1)))
        ((perfectRestrict (overlapOpen (.of (ZMod 1))).ι).obj K) :=
  laurentOverlapEquiv_symm_globalUnit_coefficient (.of (ZMod 1)) K

end QuillenTest.LaurentOverlapCoefficientBoundary
