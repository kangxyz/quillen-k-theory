/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LaurentRankOnePhiBoundary
public import QuillenTest.NativeTautologicalCoordinateCone
public import QuillenTest.NativeTautologicalConeClass

/-! The original projective boundary retains the inverse of the original Phi difference. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ProjectiveLine
open Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.LaurentRankOnePhiBoundary

/-- The exact original projective boundary is the inverse original Phi rank-one difference. -/
theorem original_boundary_inverse_Phi_difference (R : CommRingCat.{u}) :
    laurentProjectiveConnecting R 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
          (rankOnePerfect (Spec (.of (LaurentPolynomial R))))) =
      (nativeTwoSummandKMap (affineBase R) 0
        ((perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R)),
          ((perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R)))⁻¹))⁻¹ := by
  rw [laurentProjectiveConnecting_forward_rankOne_Phi, ← map_inv]
  simp only [Prod.inv_mk, inv_inv]

/-- The unchanged projective boundary cancels that original Phi difference. -/
theorem original_boundary_Phi_difference_cancel (R : CommRingCat.{u}) :
    laurentProjectiveConnecting R 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
          (rankOnePerfect (Spec (.of (LaurentPolynomial R))))) *
      nativeTwoSummandKMap (affineBase R) 0
        ((perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R)),
          ((perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R)))⁻¹) = 1 := by
  rw [original_boundary_inverse_Phi_difference]
  exact inv_mul_cancel _

/-- The original projective boundary image formula includes the zero ring. -/
theorem zero_ring_original_boundary_image :
    laurentProjectiveConnecting (.of (ZMod 1)) 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit (.of (ZMod 1)))
          (rankOnePerfect (Spec (.of (LaurentPolynomial (ZMod 1)))))) =
      nativeTwoSummandKMap (affineBase (.of (ZMod 1))) 0
        (((perfectWaldhausen (Spec (.of (ZMod 1)))).kZeroObjectClass
            (rankOnePerfect (Spec (.of (ZMod 1)))))⁻¹,
          (perfectWaldhausen (Spec (.of (ZMod 1)))).kZeroObjectClass
            (rankOnePerfect (Spec (.of (ZMod 1))))) :=
  laurentProjectiveConnecting_forward_rankOne_Phi _

end QuillenTest.LaurentRankOnePhiBoundary
