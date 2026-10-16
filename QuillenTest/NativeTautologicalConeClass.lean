/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeTautologicalConeClass
public import QuillenTest.RankOneFlatPullback
public import Mathlib.Data.ZMod.Basic

/-! Original affine coordinate-cone classes retain native Phi order and the zero ring. -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ProjectiveLine
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace QuillenTest.NativeTautologicalConeClass

/-- The inverse class of the actual native coordinate cone has coordinates (e⁻¹,e). -/
theorem actual_inverse_cone_coordinates (R : CommRingCat.{u}) :
    ((perfectWaldhausen (nativeLineFunctor.obj ⟨Spec R, inferInstance⟩).obj).kZeroObjectClass
      ((perfectRestrict (nativeAffineIso R).inv).obj
        ⟨(tautologicalCoordinateSupportedCone R).obj,
          (tautologicalCoordinateSupportedCone R).property.1⟩))⁻¹ =
      nativeTwoSummandKMap ⟨Spec R, inferInstance⟩ 0
        (((perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R)))⁻¹,
          (perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R))) := by
  rw [inverseAffineTautologicalCone_class, ← map_inv]
  simp only [Prod.inv_mk, inv_inv]

/-- The unchanged coordinate formula includes the zero ring. -/
theorem zero_ring_coordinate_cone :
    (perfectWaldhausen
      (nativeLineFunctor.obj ⟨Spec (.of (ZMod 1)), inferInstance⟩).obj).kZeroObjectClass
      ((perfectRestrict (nativeAffineIso (.of (ZMod 1))).inv).obj
        ⟨(tautologicalCoordinateSupportedCone (.of (ZMod 1))).obj,
          (tautologicalCoordinateSupportedCone (.of (ZMod 1))).property.1⟩) =
      nativeTwoSummandKMap ⟨Spec (.of (ZMod 1)), inferInstance⟩ 0
        ((perfectWaldhausen (Spec (.of (ZMod 1)))).kZeroObjectClass
          (rankOnePerfect (Spec (.of (ZMod 1)))),
          ((perfectWaldhausen (Spec (.of (ZMod 1)))).kZeroObjectClass
            (rankOnePerfect (Spec (.of (ZMod 1)))))⁻¹) :=
  inverseAffineTautologicalCone_class _

end QuillenTest.NativeTautologicalConeClass
