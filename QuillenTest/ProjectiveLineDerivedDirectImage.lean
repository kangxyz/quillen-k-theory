/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DerivedDirectImage
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of the installed bounded-below projection maps on the two original singles -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace QuillenTest.ProjectiveLineDerivedDirectImage

open Quillen
/-- The standard ambient derived category of actual module sheaves. -/
local instance standardDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

/-- Both given integer-indexed augmentations remain actual quasi-isomorphisms under projection. -/
theorem original_augmentations (R : CommRingCat.{u})
    (I : InjectiveResolution (SheafOfModules.unit (twoChartLine R).ringCatSheaf))
    (J : InjectiveResolution (tautologicalLine R)) :
    QuasiIso (((Scheme.Modules.pushforward (projection R)).mapHomologicalComplex (.up ℤ)).map
      I.ι') ∧
    QuasiIso (((Scheme.Modules.pushforward (projection R)).mapHomologicalComplex (.up ℤ)).map
      J.ι') :=
  ⟨quasiIso_projection_unit_resolution_int R I,
    quasiIso_projection_tautological_resolution_int R J⟩

/-- The structure comparison retains all three original maps, including the installed unit. -/
theorem original_structure_composite (R : CommRingCat.{u}) :
    (derivedProjectionStructureSheafIso R).hom =
      DerivedCategory.Plus.Q.map (singleZeroPlusIso (projectionUnitIso R)).hom ≫
        DerivedCategory.Plus.Q.map (pushforwardSingleZeroPlusIso (projection R) _).inv ≫
          (derivedPushforwardPlusUnit (projection R)).app
            (singleZeroPlus (twoChartLine R)
              (SheafOfModules.unit (twoChartLine R).ringCatSheaf)) :=
  derivedProjectionStructureSheafIso_hom R

/-- Maps out of the actual negative-line derived image are zero. -/
theorem original_negative_derived_map (R : CommRingCat.{u})
    (N : DerivedCategory.Plus (Spec R).Modules)
    (f : (derivedPushforwardPlus (projection R)).obj
      (DerivedCategory.Plus.Q.obj (singleZeroPlus (twoChartLine R) (tautologicalLine R))) ⟶ N) :
    f = 0 := (isZero_derivedProjection_tautologicalLine R).eq_of_src _ _

/-- The actual structure comparison detects equality of arrows from its original derived image. -/
theorem original_structure_cancellation (R : CommRingCat.{u})
    (N : DerivedCategory.Plus (Spec R).Modules)
    (a b : (derivedPushforwardPlus (projection R)).obj (DerivedCategory.Plus.Q.obj
      (singleZeroPlus (twoChartLine R) (SheafOfModules.unit (twoChartLine R).ringCatSheaf))) ⟶ N)
    (h : (derivedProjectionStructureSheafIso R).hom ≫ a =
      (derivedProjectionStructureSheafIso R).hom ≫ b) : a = b :=
  (cancel_epi (derivedProjectionStructureSheafIso R).hom).mp h

/-- The installed negative-line unit remains invertible over the zero ring. -/
theorem zero_ring_installed_unit :
    IsIso ((derivedPushforwardPlusUnit (projection (.of (ZMod 1)))).app
      (singleZeroPlus (twoChartLine (.of (ZMod 1))) (tautologicalLine (.of (ZMod 1))))) :=
  inferInstance

end QuillenTest.ProjectiveLineDerivedDirectImage
