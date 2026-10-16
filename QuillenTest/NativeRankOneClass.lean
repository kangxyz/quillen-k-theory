/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeRankOneClass
public import QuillenTest.RankOneFlatPullback
public import Mathlib.Data.ZMod.Basic
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-! Original native Phi keeps the actual rank-one class and the negative tensor order. -/
@[expose] public section
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
namespace QuillenTest.NativeRankOneClass

/-- The inverse cone class has the inverse first coefficient and the rank-one second coefficient. -/
theorem original_native_inverse_cone_coordinates
    (X : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u})
    (f : nativeTautologicalPerfect X ⟶ rankOnePerfect (nativeLineFunctor.obj X).obj) :
    ((perfectWaldhausen (nativeLineFunctor.obj X).obj).kZeroObjectClass
      ⟨CochainComplex.mappingCone f.hom,
        Scheme.Modules.Complex.locallyPerfect_mappingCone (nativeTautologicalPerfect X).property
          (rankOnePerfect _).property f.hom⟩)⁻¹ =
      nativeTwoSummandKMap X 0
        (((perfectWaldhausen X.obj).kZeroObjectClass (rankOnePerfect X.obj))⁻¹,
          (perfectWaldhausen X.obj).kZeroObjectClass (rankOnePerfect X.obj)) := by
  rw [nativeTautologicalArrow_cone_class, ← map_inv]
  simp only [Prod.inv_mk, inv_inv]

/-- The unchanged second native summand formula applies to the zero ring. -/
theorem original_zero_ring_negative_class :
    Quillen.Waldhausen.KMap (nativeSecondSummand_exact ⟨Spec (.of (ZMod 1)), inferInstance⟩) 0
      ((perfectWaldhausen (Spec (.of (ZMod 1)))).kZeroObjectClass
        (rankOnePerfect (Spec (.of (ZMod 1))))) =
      (perfectWaldhausen
        (nativeLineFunctor.obj ⟨Spec (.of (ZMod 1)), inferInstance⟩).obj).kZeroObjectClass
        (nativeTautologicalPerfect ⟨Spec (.of (ZMod 1)), inferInstance⟩) :=
  nativeSecondRankOne_class _

end QuillenTest.NativeRankOneClass
