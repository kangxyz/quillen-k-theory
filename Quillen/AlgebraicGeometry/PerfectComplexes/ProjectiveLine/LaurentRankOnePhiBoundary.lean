/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeTautologicalCoordinateCone
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeTautologicalConeClass

/-!
# The original Laurent rank-one projective boundary in the original Phi image

The actual overlap boundary, original supported excision, original affine cone and unchanged
native Phi map give the image formula Phi(e⁻¹,e). Here e denotes the actual rank-one object class.
This is an image identity for the original map; it does not apply the native global Phi inverse
and does not claim the terminal Bass sign or the full rank-one localization milestone.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.ProjectiveLine AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open FlasqueTwoSummands

/-- The original projective boundary uses Phi in the unchanged structure/negative-line order. -/
theorem laurentProjectiveConnecting_forward_rankOne_Phi (R : CommRingCat.{u}) :
    laurentProjectiveConnecting R 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
          (rankOnePerfect (Spec (.of (LaurentPolynomial R))))) =
      nativeTwoSummandKMap (affineBase R) 0
        (((perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R)))⁻¹,
          (perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R))) := by
  rw [laurentProjectiveConnecting_forward_rankOne]
  change ((perfectWaldhausen _).kZeroObjectClass
    ((perfectRestrict (nativeAffineIso R).inv).obj
      ⟨(tautologicalCoordinateSupportedCone R).obj,
        (tautologicalCoordinateSupportedCone R).property.1⟩))⁻¹ = _
  rw [inverseAffineTautologicalCone_class, ← map_inv]
  simp only [Prod.inv_mk, inv_inv]

end Quillen.PerfectComplexes.ProjectiveLine.BassPositive
