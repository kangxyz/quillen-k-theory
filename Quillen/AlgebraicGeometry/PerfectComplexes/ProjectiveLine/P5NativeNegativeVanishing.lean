/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Locality.Derived
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeProjectionPerfect
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeOpenNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeAffineTwoSummands
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativePerfectGeneration
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedPerfect


/-! # Actual native negative-line projection vanishing

The original open base-change mate and original affine coordinate comparison
reduce the actual negative pullback complex to the accepted affine calculation.
Open-cover reflection takes place in the original derived category, not on K-groups.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open AlgebraicGeometry.Scheme.ProjectiveLine


open AlgebraicGeometry.Scheme.Modules

open Quillen





noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ProjectiveLine
namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativeEntries

/-- The standard derived-category instance for sheaves of modules on `Y`. -/
local instance nativeEntriesDerived (Y : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Y.Modules := HasDerivedCategory.standard _

/-- The original pullback followed by actual left tensor with the native negative line. -/
def negativeModule (X : QuasiCompactSchemes.{u}) :
    X.obj.Modules ⥤ (nativeLineFunctor.obj X).obj.Modules :=
  Scheme.Modules.pullback (nativeProjection.app X).hom ⋙
    moduleTensorLeftFunctor (nativeLineFunctor.obj X).obj (nativeTautologicalLine X)

instance negativeModule_additive (X : QuasiCompactSchemes.{u}) :
    (negativeModule X).Additive := by
  unfold negativeModule
  infer_instance

/-- The same original negative functor on all bounded-below complexes. -/
def negativePlus (X : QuasiCompactSchemes.{u}) :
    CochainComplex.Plus X.obj.Modules ⥤ CochainComplex.Plus (nativeLineFunctor.obj X).obj.Modules :=
  (negativeModule X).mapCochainComplexPlus

/-- The affine calculation on the actual raw negative complex, with its original exact unit. -/
theorem affineNegative_derivedZero (R : CommRingCat.{u})
    (K : CochainComplex.Plus (Spec R).Modules) (hK : locallyPerfect (Spec R) K.obj) :
    IsZero ((derivedPushforwardPlus (projection R)).obj (DerivedCategory.Plus.Q.obj
      ((affineNegativePullbackModule R).mapCochainComplexPlus.obj K))) := by
  have hz := isZero_derivedProjection_negativePullback_perfect R (DerivedCategory.Plus.Q.obj K)
    ((perfectDerivedObjects_toDerived_iff (Spec R) K.obj).mpr hK)
  have := (affineNegativePullbackModule R).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  exact hz.of_iso ((derivedPushforwardPlus (projection R)).mapIso
    (asIso ((affineNegativePullbackModule R).rightDerivedFunctorPlusUnit.app K)))

/-- Original affine native coordinates retain the actual negative tensor and projection. -/
theorem nativeAffineNegative_derivedZero (R : CommRingCat.{u})
    (K : CochainComplex.Plus (Spec R).Modules) (hK : locallyPerfect (Spec R) K.obj) :
    IsZero ((derivedPushforwardPlus (nativeProjection.app ⟨Spec R, inferInstance⟩).hom).obj
      (DerivedCategory.Plus.Q.obj ((negativePlus ⟨Spec R, inferInstance⟩).obj K))) := by
  let C := (negativePlus ⟨Spec R, inferInstance⟩).obj K
  let e : (Scheme.Modules.pullback (nativeAffineIso R).hom).mapCochainComplexPlus.obj C ≅
      (affineNegativePullbackModule R).mapCochainComplexPlus.obj K :=
    (CochainComplex.plus (twoChartLine R).Modules).isoMk
      ((locallyPerfect (twoChartLine R)).ι.mapIso
        ((FlasqueTwoSummands.nativeSecondTransportIso R).app ⟨K.obj, hK⟩))
  have := isIso_derivedFlatPullbackPlusUnit (nativeAffineIso R).hom
  let eunit := asIso
    ((Scheme.Modules.pullback (nativeAffineIso R).hom).rightDerivedFunctorPlusUnit.app C)
  exact (affineNegative_derivedZero R K hK).of_iso
    (nativeAffineProjectionDerivedIso R (DerivedCategory.Plus.Q.obj C) ≪≫
      (derivedPushforwardPlus (projection R)).mapIso
        (eunit.symm ≪≫ DerivedCategory.Plus.Q.mapIso e))

/-- The original native negative pullback has zero derived projection over every qc base. -/
theorem negative_derivedZero (X : QuasiCompactSchemes.{u})
    (K : CochainComplex.Plus X.obj.Modules) (hK : locallyPerfect X.obj K.obj) :
    IsZero ((derivedPushforwardPlus (nativeProjection.app X).hom).obj
      (DerivedCategory.Plus.Q.obj ((negativePlus X).obj K))) := by
  let C := (negativePlus X).obj K
  apply isZero_of_derivedOpenCover
    (fun i => Spec (X.obj.affineOpenCover.X i)) X.obj.affineOpenCover.f
    (fun x => ⟨_, X.obj.affineOpenCover.covers x⟩)
  intro i
  let U : QuasiCompactSchemes.{u} := ⟨Spec (X.obj.affineOpenCover.X i), inferInstance⟩
  let f : U ⟶ X := ⟨X.obj.affineOpenCover.f i⟩
  let B := (Scheme.Modules.restrictFunctor f.hom).mapCochainComplexPlus.obj K
  have hB : locallyPerfect U.obj B.obj := locallyPerfect_restrict f.hom hK
  let e : (Scheme.Modules.pullback (nativeLineFunctor.map f).hom).mapCochainComplexPlus.obj C ≅
      (negativePlus U).obj B :=
    (CochainComplex.plus (nativeLineFunctor.obj U).obj.Modules).isoMk
      (((restrictIsoPullbackComplex (nativeLineFunctor.map f).hom).app C.obj).symm ≪≫
        (locallyPerfect (nativeLineFunctor.obj U).obj).ι.mapIso
          ((nativeSecondSummandOpenIso f).app ⟨K.obj, hK⟩))
  have := isIso_derivedFlatBaseChangeMap_of_open (nativeLineFunctor.map f).hom
    (nativeProjection.app U).hom (nativeProjection.app X).hom f.hom (nativeMap_isPullback f)
  have := isIso_derivedFlatPullbackPlusUnit (nativeLineFunctor.map f).hom
  let eunit := asIso
    ((Scheme.Modules.pullback (nativeLineFunctor.map f).hom).rightDerivedFunctorPlusUnit.app C)
  exact (nativeAffineNegative_derivedZero (X.obj.affineOpenCover.X i) B hB).of_iso
    (asIso ((derivedFlatBaseChangeMap (nativeLineFunctor.map f).hom
      (nativeProjection.app U).hom (nativeProjection.app X).hom f.hom
      (nativeMap_isPullback f)).app (DerivedCategory.Plus.Q.obj C)) ≪≫
      (derivedPushforwardPlus (nativeProjection.app U).hom).mapIso
        (eunit.symm ≪≫ DerivedCategory.Plus.Q.mapIso e))

end Quillen.PerfectComplexes.ProjectiveLine.P5NativeEntries
