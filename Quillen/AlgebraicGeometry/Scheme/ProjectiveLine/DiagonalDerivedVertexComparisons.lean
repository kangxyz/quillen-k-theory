/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalComplexProjectedTriangle

/-! # Original exact derived vertex comparisons for the localized diagonal triangle

The localization factors and installed exact derived units identify the first
two actual vertices with their original coefficient derived functors. The
projected comparisons keep the literal original second-projection functor.
-/
@[expose] public section
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.Pretriangulated AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
local instance vertexComparisonStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u})

/-- The original first complex triangle vertex is its actual coefficient complex. -/
def diagonalComplexFirstFunctorIso :
    diagonalComplexTensorTriangleFunctor R ⋙ Triangle.π₁ ≅
      (diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₁).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    dsimp
    rw [Category.comp_id, Category.id_comp]
    exact diagonalComplexTensorTriangleMap_hom₁ R f)

/-- The original first derived vertex is identified by the actual localization
factor and installed exact coefficient derived unit, naturally on all D+ morphisms. -/
def diagonalDerivedComplexFirstIso :
    diagonalDerivedComplexTriangleFunctor R ⋙ Triangle.π₁ ≅
      (diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₁).rightDerivedFunctorPlus := by
  let F := diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₁
  let := F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (twoChartLine R).Modules)
    (DerivedCategory.Plus (relativeSquare R).Modules)).preimageIso
  exact (associator DerivedCategory.Plus.Q (diagonalDerivedComplexTriangleFunctor R)
    Triangle.π₁).symm ≪≫
    isoWhiskerRight (diagonalDerivedComplexTriangleFactors R) Triangle.π₁ ≪≫
    diagonalComplexFirstFunctorIso R ≪≫ asIso F.rightDerivedFunctorPlusUnit

/-- The original first projected vertex remains its actual derived second image. -/
def diagonalDerivedComplexProjectedFirstIso :
    diagonalDerivedComplexProjectedTriangleFunctor R ⋙ Triangle.π₁ ≅
      (diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₁).rightDerivedFunctorPlus ⋙
        derivedPushforwardPlus (relativeSecond R) :=
  (associator (diagonalDerivedComplexTriangleFunctor R) Triangle.π₁
    (derivedPushforwardPlus (relativeSecond R))).symm ≪≫
    isoWhiskerRight (diagonalDerivedComplexFirstIso R)
      (derivedPushforwardPlus (relativeSecond R))

/-- The original second complex triangle vertex is its actual coefficient complex. -/
def diagonalComplexSecondFunctorIso :
    diagonalComplexTensorTriangleFunctor R ⋙ Triangle.π₂ ≅
      (diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₂).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    dsimp
    rw [Category.comp_id, Category.id_comp]
    exact diagonalComplexTensorTriangleMap_hom₂ R f)

/-- The original second derived vertex is identified by the actual localization
factor and installed exact coefficient derived unit, naturally on all D+ morphisms. -/
def diagonalDerivedComplexSecondIso :
    diagonalDerivedComplexTriangleFunctor R ⋙ Triangle.π₂ ≅
      (diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₂).rightDerivedFunctorPlus := by
  let F := diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₂
  let := F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (twoChartLine R).Modules)
    (DerivedCategory.Plus (relativeSquare R).Modules)).preimageIso
  exact (associator DerivedCategory.Plus.Q (diagonalDerivedComplexTriangleFunctor R)
    Triangle.π₂).symm ≪≫
    isoWhiskerRight (diagonalDerivedComplexTriangleFactors R) Triangle.π₂ ≪≫
    diagonalComplexSecondFunctorIso R ≪≫ asIso F.rightDerivedFunctorPlusUnit

/-- The original second projected vertex remains its actual derived second image. -/
def diagonalDerivedComplexProjectedSecondIso :
    diagonalDerivedComplexProjectedTriangleFunctor R ⋙ Triangle.π₂ ≅
      (diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₂).rightDerivedFunctorPlus ⋙
        derivedPushforwardPlus (relativeSecond R) :=
  (associator (diagonalDerivedComplexTriangleFunctor R) Triangle.π₂
    (derivedPushforwardPlus (relativeSecond R))).symm ≪≫
    isoWhiskerRight (diagonalDerivedComplexSecondIso R)
      (derivedPushforwardPlus (relativeSecond R))

end AlgebraicGeometry.Scheme.ProjectiveLine
