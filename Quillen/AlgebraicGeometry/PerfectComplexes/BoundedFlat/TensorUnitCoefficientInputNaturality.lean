/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientSpectrum
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportHomotopy
public import Quillen.Waldhausen.SConstruction.Iterated.RowTransformationInputNaturality

/-! # The genuine first coefficient cell on original supported inputs

Precomposition acts before both original cell directions. The supported input map
uses the actual support inclusion and its canonical zero normalization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry MonoidalCategory
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Simplicial
universe u
namespace Quillen.PerfectComplexes
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

/-- The whole first coefficient cell preserves any actual exact based input map. -/
theorem tensorUnitPullbackCoefficientStageCylinder_precomp
    {V : Model.{u + 1}} (J : V ⟶ modelOf (boundedFlatPerfectWaldhausen Y)) (k : ℕ) :
    rowTransformationCylinder
        (F := J ≫ tensorUnitPullbackModelMap f) (G := J ≫ tensorUnitPullbackModelMap f)
        (whiskerLeft J.functor (tensorUnitPullbackModelTransformation f r))
        (fun A => tensorUnitPullbackModelTransformation_weak f r (J.functor.obj A)) k =
      (((stages k).map J ▷ Δ[1]) ▷ Δ[1]) ≫
        tensorUnitPullbackCoefficientStageCylinder f r k :=
  rowTransformationCylinder_precomp (tensorUnitPullbackModelTransformation f r)
    (tensorUnitPullbackModelTransformation_weak f r) J k

variable {U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]

/-- Forget only the original supported acyclicity, retaining its actual exact inclusion. -/
def tensorCoefficientSupportedForget :
    (boundedFlatPerfectSupported j).FullSubcategory ⥤ BoundedFlatPerfect Y :=
  ObjectProperty.ιOfLE (show boundedFlatPerfectSupported j ≤ boundedFlatPerfect Y from
    fun _ h => h.1)

/-- The inherited support inclusion is exact for the original Waldhausen structures. -/
theorem tensorCoefficientSupportedForget_exact :
    IsExact (boundedFlatPerfectSupportedWaldhausen j).cof
      (boundedFlatPerfectSupportedWaldhausen j).weq
      (boundedFlatPerfectWaldhausen Y).cof (boundedFlatPerfectWaldhausen Y).weq
      (tensorCoefficientSupportedForget j) :=
  subcategoryInclusion_exact _ _ (fun _ h => h.1)

/-- The actual supported input uses precisely the original chosen-zero rebase. -/
def tensorCoefficientSupportedForgetModel :
    modelOf (boundedFlatPerfectSupportedWaldhausen j) ⟶
      modelOf (boundedFlatPerfectWaldhausen Y) :=
  modelMap _ _ (tensorCoefficientSupportedForget_exact j).rebase
    (Quillen.rebaseFunctor_obj_base _ _ _ _)

/-- On supported inputs the first-row construction retains both original time coordinates. -/
theorem tensorUnitSupportedCoefficientStageCylinder_eq (k : ℕ) :
    rowTransformationCylinder
        (F := tensorCoefficientSupportedForgetModel j ≫ tensorUnitPullbackModelMap f)
        (G := tensorCoefficientSupportedForgetModel j ≫ tensorUnitPullbackModelMap f)
        (whiskerLeft (tensorCoefficientSupportedForgetModel j).functor
          (tensorUnitPullbackModelTransformation f r))
        (fun A => tensorUnitPullbackModelTransformation_weak f r
          ((tensorCoefficientSupportedForgetModel j).functor.obj A)) k =
      (((stages k).map (tensorCoefficientSupportedForgetModel j) ▷ Δ[1]) ▷ Δ[1]) ≫
        tensorUnitPullbackCoefficientStageCylinder f r k :=
  tensorUnitPullbackCoefficientStageCylinder_precomp f r
    (tensorCoefficientSupportedForgetModel j) k

end Quillen.PerfectComplexes
