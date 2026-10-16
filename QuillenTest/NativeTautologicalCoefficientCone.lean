/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeTautologicalCoefficientCone
public import QuillenTest.LaurentOverlapCoefficientBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.TautologicalCoefficientRankOne

/-! Actual native restriction, boundary and original rank-one cone compatibility. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ProjectiveLine
open Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands
open Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open AlgebraicGeometry.Scheme.ProjectiveLine
  AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.NativeTautologicalCoefficientCone

/-- Forgetting support retains the literal original inverse-affine coefficient-cone restriction. -/
theorem forgotten_native_coefficient_is_original_restriction (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    (⟨(nativeTautologicalCoefficientSupportedCone R K).obj,
        (nativeTautologicalCoefficientSupportedCone R K).property.1⟩ :
      Perfect (nativeLineFunctor.obj (affineBase R)).obj) =
      (perfectRestrict (nativeAffineIso R).inv).obj
        ⟨(tautologicalCoefficientSupportedCone R K).obj,
          (tautologicalCoefficientSupportedCone R K).property.1⟩ := rfl

/-- The original projective boundary cancels that exact inverse-affine coefficient cone. -/
theorem native_coefficient_boundary_cancel (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    laurentProjectiveConnecting R 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
          ((perfectRestrict (laurentMinus R)).obj
            ((perfectRestrict (minusChart R)).obj K))) *
      (perfectWaldhausen (nativeLineFunctor.obj (affineBase R)).obj).kZeroObjectClass
        ((perfectRestrict (nativeAffineIso R).inv).obj
          ⟨(tautologicalCoefficientSupportedCone R K).obj,
            (tautologicalCoefficientSupportedCone R K).property.1⟩) = 1 := by
  rw [laurentProjectiveConnecting_forward_coefficient,
    forgotten_native_coefficient_is_original_restriction]
  exact inv_mul_cancel _

/-- Actual rank-one restrictions recover the previously fixed original Laurent input. -/
theorem native_rank_one_coefficient_input (R : CommRingCat.{u}) :
    perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
        ((perfectRestrict (laurentMinus R)).obj
          ((perfectRestrict (minusChart R)).obj (rankOnePerfect (twoChartLine R)))) =
      perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
        (rankOnePerfect (Spec (.of (LaurentPolynomial R)))) :=
  perfectGlobalUnitKOneClass_iso _ _
    ((perfectRestrict (laurentMinus R)).mapIso (rankOnePerfectRestrictIso (minusChart R)) ≪≫
      rankOnePerfectRestrictIso (laurentMinus R))

/-- The actual native supported class at rank one agrees with the previously fixed cone. -/
theorem native_rank_one_coefficient_class (R : CommRingCat.{u}) :
    (perfectSupportedWaldhausen (positiveOpen R).ι).kZeroObjectClass
        (nativeTautologicalCoefficientSupportedCone R (rankOnePerfect (twoChartLine R))) =
      (perfectSupportedWaldhausen (positiveOpen R).ι).kZeroObjectClass
        (nativeTautologicalCoordinateSupportedCone R) :=
  (perfectSupportedWaldhausen (positiveOpen R).ι).kZeroObjectClass_iso
    ((perfectSupported (positiveOpen R).ι).isoMk
      ((restrict (nativeAffineIso R).inv).mapIso (tautologicalCoefficientRankOneConeIso R)))

/-- Every original perfect coefficient is retained also over the zero ring. -/
theorem zero_ring_native_coefficient_boundary
    (K : Perfect (twoChartLine (.of (ZMod 1)))) :
    laurentProjectiveConnecting (.of (ZMod 1)) 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit (.of (ZMod 1)))
          ((perfectRestrict (laurentMinus (.of (ZMod 1)))).obj
            ((perfectRestrict (minusChart (.of (ZMod 1)))).obj K))) *
      (perfectWaldhausen (nativeLineFunctor.obj (affineBase (.of (ZMod 1)))).obj).kZeroObjectClass
        ((perfectRestrict (nativeAffineIso (.of (ZMod 1))).inv).obj
          ⟨(tautologicalCoefficientSupportedCone (.of (ZMod 1)) K).obj,
            (tautologicalCoefficientSupportedCone (.of (ZMod 1)) K).property.1⟩) = 1 :=
  native_coefficient_boundary_cancel (.of (ZMod 1)) K

end QuillenTest.NativeTautologicalCoefficientCone
