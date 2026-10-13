/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AcyclicDerivedPushforward
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.StructureSheafDirectImage
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalDirectImage

/-! # Actual bounded-below direct images of the original structure and negative-line singles

The installed derived unit is invertible on both original single sheaves. The structure-module
comparison uses its actual direct-image unit and the original single-complex comparison.
The negative-line derived image is zero. These are specific objects over arbitrary base rings;
no general preservation of perfect complexes by the projection is asserted.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf
/-- The standard ambient derived category used by the installed direct-image unit. -/
local instance derivedProjectionStandard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
variable (R : CommRingCat.{u})

lemma quasiIso_projection_unit_resolution_int
    (I : InjectiveResolution (SheafOfModules.unit (twoChartLine R).ringCatSheaf)) :
    QuasiIso (((Scheme.Modules.pushforward (projection R)).mapHomologicalComplex (.up ℤ)).map
      I.ι') :=
  quasiIso_pushforward_injectiveResolution_int_of_quasiIso _ _ I
    (quasiIso_pushforward_injectiveResolution_of_exact _ _ I
      (projection_unit_resolution_exact_succ R I))

lemma quasiIso_projection_tautological_resolution_int
    (I : InjectiveResolution (tautologicalLine R)) :
    QuasiIso (((Scheme.Modules.pushforward (projection R)).mapHomologicalComplex (.up ℤ)).map
      I.ι') :=
  quasiIso_pushforward_injectiveResolution_int_of_quasiIso _ _ I
    (quasiIso_pushforward_injectiveResolution_of_exact _ _ I
      (fun n => projection_tautological_resolution_exact R I (n + 1)))

instance isIso_derivedProjectionUnit_structureSheaf :
    IsIso ((derivedPushforwardPlusUnit (projection R)).app
      (singleZeroPlus (twoChartLine R) (SheafOfModules.unit (twoChartLine R).ringCatSheaf))) :=
  isIso_derivedPushforwardPlusUnit_single_of_resolution _ _ _
    (quasiIso_projection_unit_resolution_int R (injectiveResolution _))

instance isIso_derivedProjectionUnit_tautologicalLine :
    IsIso ((derivedPushforwardPlusUnit (projection R)).app
      (singleZeroPlus (twoChartLine R) (tautologicalLine R))) :=
  isIso_derivedPushforwardPlusUnit_single_of_resolution _ _ _
    (quasiIso_projection_tautological_resolution_int R (injectiveResolution _))

/-- The original structure single identified with its actual bounded-below derived image. -/
def derivedProjectionStructureSheafIso :
    DerivedCategory.Plus.Q.obj
      (singleZeroPlus (Spec R) (SheafOfModules.unit (Spec R).ringCatSheaf)) ≅
      (derivedPushforwardPlus (projection R)).obj (DerivedCategory.Plus.Q.obj
        (singleZeroPlus (twoChartLine R) (SheafOfModules.unit (twoChartLine R).ringCatSheaf))) :=
  DerivedCategory.Plus.Q.mapIso (singleZeroPlusIso (projectionUnitIso R)) ≪≫
    (DerivedCategory.Plus.Q.mapIso (pushforwardSingleZeroPlusIso (projection R) _)).symm ≪≫
      asIso ((derivedPushforwardPlusUnit (projection R)).app _)

lemma derivedProjectionStructureSheafIso_hom :
    (derivedProjectionStructureSheafIso R).hom =
      DerivedCategory.Plus.Q.map (singleZeroPlusIso (projectionUnitIso R)).hom ≫
        DerivedCategory.Plus.Q.map (pushforwardSingleZeroPlusIso (projection R) _).inv ≫
          (derivedPushforwardPlusUnit (projection R)).app
            (singleZeroPlus (twoChartLine R)
              (SheafOfModules.unit (twoChartLine R).ringCatSheaf)) := rfl

lemma isZero_derivedProjection_tautologicalLine :
    IsZero ((derivedPushforwardPlus (projection R)).obj
      (DerivedCategory.Plus.Q.obj (singleZeroPlus (twoChartLine R) (tautologicalLine R)))) := by
  let M := (Scheme.Modules.pushforward (projection R)).obj (tautologicalLine R)
  have hz : IsZero (singleZeroPlus (Spec R) M) := by
    rw [IsZero.iff_id_eq_zero]
    apply ObjectProperty.hom_ext
    exact ((CochainComplex.singleFunctor (Spec R).Modules 0).map_isZero
      (isZero_pushforward_projection_tautologicalLine R)).eq_of_src _ _
  let : (DerivedCategory.Plus.Q (C := (Spec R).Modules)).Additive := by
    dsimp [DerivedCategory.Plus.Q]
    infer_instance
  have hq := (DerivedCategory.Plus.Q (C := (Spec R).Modules)).map_isZero hz
  exact hq.of_iso
    ((asIso ((derivedPushforwardPlusUnit (projection R)).app
      (singleZeroPlus (twoChartLine R) (tautologicalLine R)))).symm ≪≫
      DerivedCategory.Plus.Q.mapIso (pushforwardSingleZeroPlusIso (projection R) _))

end Quillen.Scheme.ProjectiveLine
