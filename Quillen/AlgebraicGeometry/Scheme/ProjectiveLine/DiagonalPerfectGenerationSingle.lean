/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalPerfectGenerationRotation
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalComplexSingleComparison
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalLineRotation
public import Quillen.AlgebraicGeometry.PerfectComplexes.Single

/-! # Explicit recovery of the original bundle-single generation and rotation triangles

Every comparison below is a composition of specified original triangle
isomorphisms, not an arbitrary completion of a triangle or a chosen strict model.
-/
@[expose] public section

open AlgebraicGeometry
open CategoryTheory.Pretriangulated
open Quillen.PerfectComplexes

open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.Pretriangulated AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
/-- The standard derived-category instance for sheaves of modules on `X`. -/
local instance generationSingleStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u}) (E : (twoChartLine R).Modules)
  [IsFiniteLocallyFree (twoChartLine R) E]

/-- The actual original vector-bundle single as an intrinsic-perfect D+ input. -/
def originalPerfectPlusSingle : OriginalPerfectPlus R :=
  ⟨DerivedCategory.Plus.Q.obj (singleZeroPlus (twoChartLine R) E),
    (perfectDerivedObjects_toDerived_iff (twoChartLine R)
      (singleZeroPlus (twoChartLine R) E).obj).mpr
      (locallyPerfect_of_strictPerfect (single_strictPerfect_int E 0))⟩

/-- The actual new projected coefficient triangle at a single input is the
maintained ORIGINAL coefficient single triangle, through its original SES comparison. -/
def diagonalDerivedCoefficientSingleIso :
    diagonalDerivedComplexCoefficientTriangle R (originalPerfectPlusSingle R E).obj ≅
      diagonalCoefficientTensorTriangle R E :=
  (diagonalCoefficientToProjectedNatIso R).app (originalPerfectPlusSingle R E).obj ≪≫
    (derivedPushforwardPlus (relativeSecond R)).mapTriangle.mapIso
      (diagonalDerivedComplexSingleTriangleIso R E) ≪≫
    (diagonalCoefficientToRawIso R E).symm

/-- The FULL intrinsic-perfect generation triangle recovers the existing original
bundle-single generation triangle with both original endpoint identifications and connecting map. -/
def diagonalPerfectGenerationSingleIso :
    diagonalPerfectGenerationTriangle R (originalPerfectPlusSingle R E) ≅
      diagonalGenerationTriangle R E :=
  (diagonalPerfectGenerationToOriginalNatIso R).app (originalPerfectPlusSingle R E) ≪≫
    diagonalDerivedCoefficientSingleIso R E ≪≫ (diagonalGenerationTriangleIso R E).symm

/-- Exact original line tensor and original signed rotation preserve the
specified full original bundle-single comparison. -/
def diagonalOriginalLineRotatedSingleIso :
    (diagonalOriginalLineRotatedFunctor R).obj (originalPerfectPlusSingle R E) ≅
      diagonalLineRotatedTriangle R E :=
  (CategoryTheory.Pretriangulated.rotate _).mapIso
    ((originalLeftLineDerived R).mapTriangle.mapIso (diagonalPerfectGenerationSingleIso R E))

/-- The final contracted triangle recovers the ORIGINAL bundle-single line-rotated
triangle by its displayed determinant contractions, exact shift comparison and original SES iso. -/
def diagonalRotatedGenerationSingleIso :
    diagonalRotatedGenerationTriangle R (originalPerfectPlusSingle R E) ≅
      diagonalLineRotatedTriangle R E :=
  (diagonalRotatedGenerationToOriginalIso R).app (originalPerfectPlusSingle R E) ≪≫
    diagonalOriginalLineRotatedSingleIso R E
end AlgebraicGeometry.Scheme.ProjectiveLine
