/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalDerivedVertexComparisons

/-! # Exact original vertex comparison units

The localization-preimage vertex isos retain the original triangle factors and
installed coefficient derived units on every bounded-below complex.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.Pretriangulated AlgebraicGeometry
namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf

local instance vertexUnitsStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable (R : CommRingCat.{u})

/-- The ORIGINAL first vertex iso retains its triangle factor and exact derived unit. -/
theorem diagonalDerivedComplexFirstIso_factors
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    (diagonalDerivedComplexFirstIso R).hom.app (DerivedCategory.Plus.Q.obj K) =
      ((diagonalDerivedComplexTriangleFactors R).hom.app K).hom₁ ≫
        (diagonalComplexFirstFunctorIso R).hom.app K ≫
          (diagonalCoefficientFunctor R
            (diagonalIncidenceSequence R).X₁).rightDerivedFunctorPlusUnit.app K := by
  let F := diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₁
  let := F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let e : DerivedCategory.Plus.Q ⋙
      (diagonalDerivedComplexTriangleFunctor R ⋙ Triangle.π₁) ≅
      DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus :=
    (associator DerivedCategory.Plus.Q (diagonalDerivedComplexTriangleFunctor R)
      Triangle.π₁).symm ≪≫
    isoWhiskerRight (diagonalDerivedComplexTriangleFactors R) Triangle.π₁ ≪≫
    diagonalComplexFirstFunctorIso R ≪≫ asIso F.rightDerivedFunctorPlusUnit
  have he := congrArg (fun α => α.app K)
    ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Q
      (CochainComplex.Plus.quasiIso (twoChartLine R).Modules)
      (DerivedCategory.Plus (relativeSquare R).Modules)).map_preimage e.hom)
  change (diagonalDerivedComplexFirstIso R).hom.app (DerivedCategory.Plus.Q.obj K) =
    e.hom.app K at he
  rw [he]
  dsimp [e]
  simp only [Category.id_comp]
  rfl

/-- The ORIGINAL second vertex iso retains its triangle factor and exact derived unit. -/
theorem diagonalDerivedComplexSecondIso_factors
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    (diagonalDerivedComplexSecondIso R).hom.app (DerivedCategory.Plus.Q.obj K) =
      ((diagonalDerivedComplexTriangleFactors R).hom.app K).hom₂ ≫
        (diagonalComplexSecondFunctorIso R).hom.app K ≫
          (diagonalCoefficientFunctor R
            (diagonalIncidenceSequence R).X₂).rightDerivedFunctorPlusUnit.app K := by
  let F := diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₂
  let := F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let e : DerivedCategory.Plus.Q ⋙
      (diagonalDerivedComplexTriangleFunctor R ⋙ Triangle.π₂) ≅
      DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus :=
    (associator DerivedCategory.Plus.Q (diagonalDerivedComplexTriangleFunctor R)
      Triangle.π₂).symm ≪≫
    isoWhiskerRight (diagonalDerivedComplexTriangleFactors R) Triangle.π₂ ≪≫
    diagonalComplexSecondFunctorIso R ≪≫ asIso F.rightDerivedFunctorPlusUnit
  have he := congrArg (fun α => α.app K)
    ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Q
      (CochainComplex.Plus.quasiIso (twoChartLine R).Modules)
      (DerivedCategory.Plus (relativeSquare R).Modules)).map_preimage e.hom)
  change (diagonalDerivedComplexSecondIso R).hom.app (DerivedCategory.Plus.Q.obj K) =
    e.hom.app K at he
  rw [he]
  dsimp [e]
  simp only [Category.id_comp]
  rfl

end Quillen.Scheme.ProjectiveLine
