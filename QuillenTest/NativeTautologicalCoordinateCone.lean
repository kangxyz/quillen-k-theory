/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeTautologicalCoordinateCone
public import Mathlib.Data.ZMod.Basic

/-! The original native projective boundary cancels the actual inverse-affine cone class. -/
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
namespace QuillenTest.NativeTautologicalCoordinateCone

/-- Support forgetting retains exactly the original inverse-affine perfect restriction. -/
theorem forgotten_native_cone_is_original_restriction (R : CommRingCat.{u}) :
    (⟨(nativeTautologicalCoordinateSupportedCone R).obj,
        (nativeTautologicalCoordinateSupportedCone R).property.1⟩ :
      Perfect (nativeLineFunctor.obj (affineBase R)).obj) =
      (perfectRestrict (nativeAffineIso R).inv).obj
        ⟨(tautologicalCoordinateSupportedCone R).obj,
          (tautologicalCoordinateSupportedCone R).property.1⟩ := rfl

/-- The unchanged projective boundary cancels its exact native supported cone after forgetting. -/
theorem native_boundary_cone_cancel (R : CommRingCat.{u}) :
    laurentProjectiveConnecting R 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
          (rankOnePerfect (Spec (.of (LaurentPolynomial R))))) *
      (perfectWaldhausen (nativeLineFunctor.obj (affineBase R)).obj).kZeroObjectClass
        ((perfectRestrict (nativeAffineIso R).inv).obj
          ⟨(tautologicalCoordinateSupportedCone R).obj,
            (tautologicalCoordinateSupportedCone R).property.1⟩) = 1 := by
  rw [laurentProjectiveConnecting_forward_rankOne,
    forgotten_native_cone_is_original_restriction]
  exact inv_mul_cancel _

/-- The support and excision identification uses no nonzero-ring assumption. -/
theorem zero_ring_native_boundary_cone_cancel :
    laurentProjectiveConnecting (.of (ZMod 1)) 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit (.of (ZMod 1)))
          (rankOnePerfect (Spec (.of (LaurentPolynomial (ZMod 1)))))) *
      (perfectWaldhausen (nativeLineFunctor.obj (affineBase (.of (ZMod 1)))).obj).kZeroObjectClass
        ((perfectRestrict (nativeAffineIso (.of (ZMod 1))).inv).obj
          ⟨(tautologicalCoordinateSupportedCone (.of (ZMod 1))).obj,
            (tautologicalCoordinateSupportedCone (.of (ZMod 1))).property.1⟩) = 1 :=
  native_boundary_cone_cancel _

end QuillenTest.NativeTautologicalCoordinateCone
