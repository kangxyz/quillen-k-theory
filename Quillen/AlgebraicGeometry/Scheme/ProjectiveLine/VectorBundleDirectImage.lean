/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.AffineRetract
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.Pullback
public import Quillen.Algebra.Homology.CochainComplexPlusSingle
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DerivedDirectImage
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TwistMinusUnit

/-! # Original direct-image comparisons for affine vector bundles on the two-chart line

The original geometric adjunction unit identifies an affine vector bundle with the ordinary
direct image of its pullback. The installed derived unit is invertible on that pullback and on
its actual negative twist. The latter has zero bounded-below derived direct image. All results
hold over arbitrary commutative rings, by literal finite-free retracts and naturality.
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.SchemeSheaf
/-- The geometric adjunction unit on the structure module is its original ringed-site unit. -/
theorem pullbackAdjunctionUnit_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit Y.ringCatSheaf) ≫
      (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  have : (TopologicalSpace.Opens.map f.base).Final := inferInstance
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom
end Quillen.SchemeSheaf
namespace Quillen.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts
open SchemeSheaf
/-- The original geometric adjunction unit is invertible on the base structure module. -/
theorem isIso_projectionAdjunctionUnit_unit (R : CommRingCat.{u}) :
    IsIso ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
      (projection R)).unit.app (SheafOfModules.unit (Spec R).ringCatSheaf)) := by
  have h := pullbackAdjunctionUnit_unit (projection R)
  have : IsIso (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
      (projection R)).unit.app (SheafOfModules.unit (Spec R).ringCatSheaf)) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforward (projection R)).map
        (pullbackUnitIso (projection R)).hom) := by
    rw [h]
    exact projectionUnitMap_isIso R
  exact IsIso.of_isIso_comp_right _
    ((AlgebraicGeometry.Scheme.Modules.pushforward (projection R)).map
      (pullbackUnitIso (projection R)).hom)
/-- The original adjunction unit identifies any affine vector bundle with the
ordinary direct image of its actual pullback to the two-chart projective line. -/
theorem isIso_projectionAdjunctionUnit_bundle (R : CommRingCat.{u})
    (M : (Spec R).Modules) [IsFiniteLocallyFree (Spec R) M] :
    IsIso ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
      (projection R)).unit.app M) := by
  have := isIso_projectionAdjunctionUnit_unit R
  exact isIso_app_affineBundle_of_unit_general R _ _ _ M

/-- The standard derived category for the actual installed unit. -/
local instance bundleStandard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
attribute [local instance] Abelian.hasFiniteBiproducts
/-- Additive images of affine bundles inherit the original derived-unit comparison
from the image of the structure module. -/
theorem isIso_derivedProjectionUnit_additive_bundle (R : CommRingCat.{u})
    (H : (Spec R).Modules ⥤ (twoChartLine R).Modules) [H.Additive]
    [IsIso ((derivedPushforwardPlusUnit (projection R)).app
      (singleZeroPlus (twoChartLine R) (H.obj (SheafOfModules.unit (Spec R).ringCatSheaf))))]
    (M : (Spec R).Modules) [IsFiniteLocallyFree (Spec R) M] :
    IsIso ((derivedPushforwardPlusUnit (projection R)).app
      (singleZeroPlus (twoChartLine R) (H.obj M))) := by
  let : (derivedPushforwardPlus (projection R)).Additive := by
    dsimp [derivedPushforwardPlus]
    infer_instance
  let K := H ⋙ CochainComplex.singleFunctorPlus (twoChartLine R).Modules 0
  let : K.Additive := by
    dsimp [K]
    infer_instance
  let α := Functor.whiskerLeft K (derivedPushforwardPlusUnit (projection R))
  let : (DerivedCategory.Plus.Q (C := (Spec R).Modules)).Additive := by
    dsimp [DerivedCategory.Plus.Q]
    infer_instance
  let : (DerivedCategory.Plus.Q (C := (twoChartLine R).Modules)).Additive := by
    dsimp [DerivedCategory.Plus.Q]
    infer_instance
  have : IsIso (α.app (SheafOfModules.unit (Spec R).ringCatSheaf)) := by
    change IsIso ((derivedPushforwardPlusUnit (projection R)).app
      (singleZeroPlus (twoChartLine R) (H.obj (SheafOfModules.unit (Spec R).ringCatSheaf))))
    infer_instance
  exact isIso_app_affineBundle_of_unit_general R _ _ α M
/-- The installed derived unit is invertible on the actual projection pullback of a bundle. -/
theorem isIso_derivedProjectionUnit_pullback_bundle (R : CommRingCat.{u})
    (M : (Spec R).Modules) [IsFiniteLocallyFree (Spec R) M] :
    IsIso ((derivedPushforwardPlusUnit (projection R)).app
      (singleZeroPlus (twoChartLine R)
        ((AlgebraicGeometry.Scheme.Modules.pullback (projection R)).obj M))) := by
  have : IsIso ((derivedPushforwardPlusUnit (projection R)).app
      (singleZeroPlus (twoChartLine R)
        ((AlgebraicGeometry.Scheme.Modules.pullback (projection R)).obj
          (SheafOfModules.unit (Spec R).ringCatSheaf)))) := by
    rw [NatTrans.isIso_app_iff_of_iso _ (singleZeroPlusIso (pullbackUnitIso (projection R)))]
    infer_instance
  exact isIso_derivedProjectionUnit_additive_bundle R _ M
/-- The installed derived unit is invertible on the actual negative twist
of a pulled-back bundle. -/
theorem isIso_derivedProjectionUnit_twisted_bundle (R : CommRingCat.{u})
    (M : (Spec R).Modules) [IsFiniteLocallyFree (Spec R) M] :
    IsIso ((derivedPushforwardPlusUnit (projection R)).app
      (singleZeroPlus (twoChartLine R)
        (twistMinus R ((AlgebraicGeometry.Scheme.Modules.pullback (projection R)).obj M)))) := by
  let H := AlgebraicGeometry.Scheme.Modules.pullback (projection R) ⋙ twistMinusFunctor R
  let : H.Additive := by dsimp [H]; infer_instance
  let e : H.obj (SheafOfModules.unit (Spec R).ringCatSheaf) ≅ tautologicalLine R :=
    (twistMinusFunctor R).mapIso (pullbackUnitIso (projection R)) ≪≫ twistMinusUnitIso R
  have : IsIso ((derivedPushforwardPlusUnit (projection R)).app
      (singleZeroPlus (twoChartLine R) (H.obj (SheafOfModules.unit (Spec R).ringCatSheaf)))) := by
    rw [NatTrans.isIso_app_iff_of_iso _ (singleZeroPlusIso e)]
    infer_instance
  exact isIso_derivedProjectionUnit_additive_bundle R H M
/-- Actual negative-twisted affine bundles have zero bounded-below derived direct image. -/
theorem isZero_derivedProjection_twisted_bundle (R : CommRingCat.{u})
    (M : (Spec R).Modules) [IsFiniteLocallyFree (Spec R) M] :
    IsZero ((derivedPushforwardPlus (projection R)).obj (DerivedCategory.Plus.Q.obj
      (singleZeroPlus (twoChartLine R)
        (twistMinus R ((AlgebraicGeometry.Scheme.Modules.pullback (projection R)).obj M))))) := by
  let H := AlgebraicGeometry.Scheme.Modules.pullback (projection R) ⋙ twistMinusFunctor R
  let : H.Additive := by dsimp [H]; infer_instance
  let : (DerivedCategory.Plus.Q (C := (twoChartLine R).Modules)).Additive := by
    dsimp [DerivedCategory.Plus.Q]
    infer_instance
  let : (derivedPushforwardPlus (projection R)).Additive := by
    dsimp [derivedPushforwardPlus]
    infer_instance
  let F := H ⋙ CochainComplex.singleFunctorPlus (twoChartLine R).Modules 0 ⋙
    DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus (projection R)
  let : F.Additive := by dsimp [F]; infer_instance
  let e : H.obj (SheafOfModules.unit (Spec R).ringCatSheaf) ≅ tautologicalLine R :=
    (twistMinusFunctor R).mapIso (pullbackUnitIso (projection R)) ≪≫ twistMinusUnitIso R
  apply isZero_obj_affineBundle_of_unit R F _ M
  exact (isZero_derivedProjection_tautologicalLine R).of_iso
    ((derivedPushforwardPlus (projection R)).mapIso
      (DerivedCategory.Plus.Q.mapIso (singleZeroPlusIso e)))

/-- The affine bundle comparison uses the original geometric adjunction unit,
the original single-complex comparison, and the installed right-derived unit. -/
def derivedProjectionPullbackBundleIso (R : CommRingCat.{u})
    (M : (Spec R).Modules) [IsFiniteLocallyFree (Spec R) M] :
    DerivedCategory.Plus.Q.obj (singleZeroPlus (Spec R) M) ≅
      (derivedPushforwardPlus (projection R)).obj (DerivedCategory.Plus.Q.obj
        (singleZeroPlus (twoChartLine R)
          ((AlgebraicGeometry.Scheme.Modules.pullback (projection R)).obj M))) := by
  have := isIso_projectionAdjunctionUnit_bundle R M
  have := isIso_derivedProjectionUnit_pullback_bundle R M
  exact DerivedCategory.Plus.Q.mapIso (singleZeroPlusIso
      (asIso ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
        (projection R)).unit.app M))) ≪≫
    (DerivedCategory.Plus.Q.mapIso (pushforwardSingleZeroPlusIso (projection R) _)).symm ≪≫
      asIso ((derivedPushforwardPlusUnit (projection R)).app _)
/-- The comparison retains the original geometric and derived unit maps. -/
theorem derivedProjectionPullbackBundleIso_hom (R : CommRingCat.{u})
    (M : (Spec R).Modules) [IsFiniteLocallyFree (Spec R) M] :
    (derivedProjectionPullbackBundleIso R M).hom =
      DerivedCategory.Plus.Q.map ((CochainComplex.singleFunctorPlus (Spec R).Modules 0).map
        ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
          (projection R)).unit.app M)) ≫
      DerivedCategory.Plus.Q.map (pushforwardSingleZeroPlusIso (projection R)
        ((AlgebraicGeometry.Scheme.Modules.pullback (projection R)).obj M)).inv ≫
      (derivedPushforwardPlusUnit (projection R)).app
        (singleZeroPlus (twoChartLine R)
          ((AlgebraicGeometry.Scheme.Modules.pullback (projection R)).obj M)) := rfl
end Quillen.Scheme.ProjectiveLine
