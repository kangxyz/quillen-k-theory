/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedFlatPullback


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Identity
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueCoefficientZero
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LineTensor
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.NativeBaseChange
public import Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.Derived.OpenImmersion
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.IsomorphismFunctors
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedPerfect

/-! # Perfection of the original native projective-line direct image

The affine P2 theorem is transported through the original native affine
isomorphism and descended along an actual affine open cover. All comparisons
use the installed derived units and original cartesian base-change mate.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open AlgebraicGeometry.Scheme.ProjectiveLine


open AlgebraicGeometry.Scheme.Modules

open Quillen





noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ProjectiveLine
namespace Quillen.PerfectComplexes.ProjectiveLine

attribute [local instance] nativeProjectionPerfectStandard

/-- The original native affine comparison gives a cartesian square over the identity base. -/
theorem nativeAffineProjection_isPullback (R : CommRingCat.{u}) :
    IsPullback (nativeAffineIso R).hom (projection R)
      (nativeProjection.app ⟨Spec R, inferInstance⟩).hom (𝟙 (Spec R)) :=
  IsPullback.of_horiz_isIso ⟨by simp only [nativeAffineIso_projection, Category.comp_id]⟩

/-- The native affine direct image is compared by the actual open-base-change mate. -/
def nativeAffineProjectionDerivedIso (R : CommRingCat.{u})
    (K : DerivedCategory.Plus (nativeLineFunctor.obj ⟨Spec R, inferInstance⟩).obj.Modules) :
    (derivedPushforwardPlus (nativeProjection.app ⟨Spec R, inferInstance⟩).hom).obj K ≅
      (derivedPushforwardPlus (projection R)).obj
        ((derivedFlatPullbackPlus (nativeAffineIso R).hom).obj K) := by
  have := isIso_derivedFlatBaseChangeMap_of_open (nativeAffineIso R).hom (projection R)
    (nativeProjection.app ⟨Spec R, inferInstance⟩).hom (𝟙 (Spec R))
    (nativeAffineProjection_isPullback R)
  exact ((derivedFlatPullbackPlusIdIso (Spec R)).app _).symm ≪≫
    asIso ((derivedFlatBaseChangeMap (nativeAffineIso R).hom (projection R)
      (nativeProjection.app ⟨Spec R, inferInstance⟩).hom (𝟙 (Spec R))
      (nativeAffineProjection_isPullback R)).app K)

/-- Affine P2 applies to the original native projection with no supplied strict model. -/
theorem perfect_nativeAffineProjection (R : CommRingCat.{u})
    (K : DerivedCategory.Plus (nativeLineFunctor.obj ⟨Spec R, inferInstance⟩).obj.Modules)
    (hK : perfectDerivedObjects (nativeLineFunctor.obj ⟨Spec R, inferInstance⟩).obj
      (DerivedCategory.Plus.ι.obj K)) :
    perfectDerivedObjects (Spec R) (DerivedCategory.Plus.ι.obj
      ((derivedPushforwardPlus (nativeProjection.app ⟨Spec R, inferInstance⟩).hom).obj K)) := by
  exact (perfectDerivedObjects (Spec R)).prop_of_iso
    (DerivedCategory.Plus.ι.mapIso (nativeAffineProjectionDerivedIso R K).symm)
    (perfect_derivedProjection_of_perfect R _
      (perfect_derivedFlatPullbackPlus (nativeAffineIso R).hom K hK))

/-- Affine P2 descends along the canonical open base-change mates for the native projection. -/
theorem perfect_nativeProjection (X : QuasiCompactSchemes.{u})
    (K : DerivedCategory.Plus (nativeLineFunctor.obj X).obj.Modules)
    (hK : perfectDerivedObjects (nativeLineFunctor.obj X).obj
      (DerivedCategory.Plus.ι.obj K)) :
    perfectDerivedObjects X.obj (DerivedCategory.Plus.ι.obj
      ((derivedPushforwardPlus (nativeProjection.app X).hom).obj K)) := by
  apply perfectDerivedObjects_of_openImmersionCover
    (fun i => Spec (X.obj.affineOpenCover.X i)) X.obj.affineOpenCover.f
    (fun x => ⟨_, X.obj.affineOpenCover.covers x⟩)
  intro i
  let U : QuasiCompactSchemes.{u} := ⟨Spec (X.obj.affineOpenCover.X i), inferInstance⟩
  let f : U ⟶ X := ⟨X.obj.affineOpenCover.f i⟩
  have := isIso_derivedFlatBaseChangeMap_of_open (nativeLineFunctor.map f).hom
    (nativeProjection.app U).hom (nativeProjection.app X).hom f.hom
    (nativeMap_isPullback f)
  exact (perfectDerivedObjects U.obj).prop_of_iso
    (DerivedCategory.Plus.ι.mapIso
      (asIso ((derivedFlatBaseChangeMap (nativeLineFunctor.map f).hom
        (nativeProjection.app U).hom (nativeProjection.app X).hom f.hom
        (nativeMap_isPullback f)).app K)).symm)
    (perfect_nativeAffineProjection (X.obj.affineOpenCover.X i) _
      (perfect_derivedFlatPullbackPlus (nativeLineFunctor.map f).hom K hK))

/-- The literal ordinary pushforward of the original flasque perfect model is locally perfect. -/
theorem locallyPerfect_nativeProjection_flasque (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj) :
    locallyPerfect X.obj
      (((Scheme.Modules.pushforward (nativeProjection.app X).hom).mapHomologicalComplex
        (.up ℤ)).obj K.obj) := by
  let P := (FlasqueCoefficients.toPlus (nativeLineFunctor.obj X).obj).obj K
  have hP : perfectDerivedObjects (nativeLineFunctor.obj X).obj
      (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj P)) :=
    (perfectDerivedObjects_toDerived_iff (nativeLineFunctor.obj X).obj K.obj).mpr
      K.property.1.1
  have hRp := perfect_nativeProjection X (DerivedCategory.Plus.Q.obj P) hP
  apply (perfectDerivedObjects_toDerived_iff X.obj _).mp
  exact (perfectDerivedObjects X.obj).prop_of_iso
    (DerivedCategory.Plus.ι.mapIso
      ((FlasqueCoefficients.derivedPushforwardIso (nativeProjection.app X).hom).app K).symm)
    hRp

end Quillen.PerfectComplexes.ProjectiveLine
