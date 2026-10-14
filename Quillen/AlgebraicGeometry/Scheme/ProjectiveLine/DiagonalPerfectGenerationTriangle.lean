/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalPerfectGenerationEndpoints
public import Quillen.CategoryTheory.Triangulated.EndpointTransport

/-! # The natural FULL original generation triangle on intrinsic perfect D+

Transport the literal original projected coefficient triangle through its
specified ORIGINAL first/second endpoint maps. Original incidence, quotient,
connecting arrows and derived roofs remain under the displayed natural iso.
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
local instance fullGenerationStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u})

/-- The specified coefficient identification is natural as an iso of actual triangle functors. -/
def diagonalCoefficientToProjectedNatIso :
    diagonalDerivedComplexCoefficientTriangleFunctor R ≅
      diagonalDerivedComplexProjectedTriangleFunctor R :=
  NatIso.ofComponents (diagonalDerivedComplexCoefficientTriangleIso R) (fun f => by
    change (_ ≫ _ ≫ _) ≫ _ = _ ≫ _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- The original first endpoint map lands in the literal coefficient triangle's first vertex. -/
def diagonalPerfectGenerationCoefficientFirstIso :
    originalPerfectPlusInclusion R ⋙ diagonalPerfectGenerationFirstFunctor R ≅
      originalPerfectPlusInclusion R ⋙
        diagonalDerivedComplexCoefficientTriangleFunctor R ⋙ Triangle.π₁ :=
  diagonalPerfectGenerationFirstIso R ≪≫
    isoWhiskerLeft (originalPerfectPlusInclusion R)
      (isoWhiskerRight (diagonalCoefficientToProjectedNatIso R) Triangle.π₁).symm

/-- The original second endpoint map lands in the literal coefficient triangle's second vertex. -/
def diagonalPerfectGenerationCoefficientSecondIso :
    originalPerfectPlusInclusion R ⋙ diagonalPerfectGenerationSecondFunctor R ≅
      originalPerfectPlusInclusion R ⋙
        diagonalDerivedComplexCoefficientTriangleFunctor R ⋙ Triangle.π₂ :=
  diagonalPerfectGenerationSecondIso R ≪≫
    isoWhiskerLeft (originalPerfectPlusInclusion R)
      (isoWhiskerRight (diagonalCoefficientToProjectedNatIso R) Triangle.π₂).symm

/-- The exact third coefficient functor retains the original right-Q maps. -/
def diagonalPerfectGenerationCoefficientThirdIso :
    originalPerfectPlusInclusion R ⋙
        (moduleTensorRightFunctor (twoChartLine R)
          (tautologicalQuotientLine R)).rightDerivedFunctorPlus ≅
      (originalPerfectPlusInclusion R ⋙
        diagonalDerivedComplexCoefficientTriangleFunctor R) ⋙ Triangle.π₃ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    dsimp
    rw [Category.id_comp, Category.comp_id]
    exact (diagonalDerivedComplexCoefficientTriangleMap_hom₃ R f.hom).symm)

/-- The FULL original incidence arrow, transported only by the original endpoint isos. -/
def diagonalPerfectGenerationIncidence :
    originalPerfectPlusInclusion R ⋙ diagonalPerfectGenerationFirstFunctor R ⟶
      originalPerfectPlusInclusion R ⋙ diagonalPerfectGenerationSecondFunctor R :=
  (diagonalPerfectGenerationCoefficientFirstIso R).hom ≫
    whiskerLeft (originalPerfectPlusInclusion R ⋙
      diagonalDerivedComplexCoefficientTriangleFunctor R) Triangle.π₁Toπ₂ ≫
    (diagonalPerfectGenerationCoefficientSecondIso R).inv

/-- The FULL original quotient arrow, transported by its specified endpoint isos. -/
def diagonalPerfectGenerationQuotient :
    originalPerfectPlusInclusion R ⋙ diagonalPerfectGenerationSecondFunctor R ⟶
      originalPerfectPlusInclusion R ⋙
        (moduleTensorRightFunctor (twoChartLine R)
          (tautologicalQuotientLine R)).rightDerivedFunctorPlus :=
  (diagonalPerfectGenerationCoefficientSecondIso R).hom ≫
    whiskerLeft (originalPerfectPlusInclusion R ⋙
      diagonalDerivedComplexCoefficientTriangleFunctor R) Triangle.π₂Toπ₃ ≫
    (diagonalPerfectGenerationCoefficientThirdIso R).inv

/-- The FULL original connecting map, with the installed original shift comparison. -/
def diagonalPerfectGenerationConnecting :
    originalPerfectPlusInclusion R ⋙
        (moduleTensorRightFunctor (twoChartLine R)
          (tautologicalQuotientLine R)).rightDerivedFunctorPlus ⟶
      (originalPerfectPlusInclusion R ⋙ diagonalPerfectGenerationFirstFunctor R) ⋙
        shiftFunctor (DerivedCategory.Plus (twoChartLine R).Modules) (1 : ℤ) :=
  (diagonalPerfectGenerationCoefficientThirdIso R).hom ≫
    whiskerLeft (originalPerfectPlusInclusion R ⋙
      diagonalDerivedComplexCoefficientTriangleFunctor R) Triangle.π₃Toπ₁ ≫
    whiskerRight (diagonalPerfectGenerationCoefficientFirstIso R).inv
      (shiftFunctor (DerivedCategory.Plus (twoChartLine R).Modules) (1 : ℤ))

/-- The FULL generation triangle on actual intrinsic perfect D+ inputs and original roofs. -/
def diagonalPerfectGenerationTriangleFunctor :
    OriginalPerfectPlus R ⥤ Triangle (DerivedCategory.Plus (twoChartLine R).Modules) :=
  Quillen.TriangleTransport.functor
    (originalPerfectPlusInclusion R ⋙ diagonalDerivedComplexCoefficientTriangleFunctor R)
    (diagonalPerfectGenerationCoefficientFirstIso R)
    (diagonalPerfectGenerationCoefficientSecondIso R)
    (diagonalPerfectGenerationCoefficientThirdIso R)

/-- The FULL triangle retains the literal original coefficient triangle naturally. -/
def diagonalPerfectGenerationToOriginalNatIso :
    diagonalPerfectGenerationTriangleFunctor R ≅
      originalPerfectPlusInclusion R ⋙ diagonalDerivedComplexCoefficientTriangleFunctor R :=
  Quillen.TriangleTransport.iso
    (originalPerfectPlusInclusion R ⋙ diagonalDerivedComplexCoefficientTriangleFunctor R)
    (diagonalPerfectGenerationCoefficientFirstIso R)
    (diagonalPerfectGenerationCoefficientSecondIso R)
    (diagonalPerfectGenerationCoefficientThirdIso R)

/-- The actual FULL original generation triangle at an intrinsic-perfect input. -/
abbrev diagonalPerfectGenerationTriangle (K : OriginalPerfectPlus R) :=
  (diagonalPerfectGenerationTriangleFunctor R).obj K

/-- The FULL original generation triangle is distinguished
at every actual intrinsic-perfect input. -/
theorem diagonalPerfectGenerationTriangle_distinguished (K : OriginalPerfectPlus R) :
    diagonalPerfectGenerationTriangle R K ∈
      distTriang (DerivedCategory.Plus (twoChartLine R).Modules) :=
  isomorphic_distinguished _
    (diagonalDerivedComplexCoefficientTriangle_distinguished R K.obj) _
    ((diagonalPerfectGenerationToOriginalNatIso R).app K)

/-- The first map is the original p*Rp*(K tensor L) map under every derived roof. -/
@[simp] theorem diagonalPerfectGenerationTriangleMap_hom₁
    {K L : OriginalPerfectPlus R} (f : K ⟶ L) :
    ((diagonalPerfectGenerationTriangleFunctor R).map f).hom₁ =
      (diagonalPerfectGenerationFirstFunctor R).map f.hom := rfl

/-- The second map is the original Q tensor p*Rp*K map under every derived roof. -/
@[simp] theorem diagonalPerfectGenerationTriangleMap_hom₂
    {K L : OriginalPerfectPlus R} (f : K ⟶ L) :
    ((diagonalPerfectGenerationTriangleFunctor R).map f).hom₂ =
      (diagonalPerfectGenerationSecondFunctor R).map f.hom := rfl

/-- The third map remains the specified original derived right-Q coefficient map. -/
@[simp] theorem diagonalPerfectGenerationTriangleMap_hom₃
    {K L : OriginalPerfectPlus R} (f : K ⟶ L) :
    ((diagonalPerfectGenerationTriangleFunctor R).map f).hom₃ =
      (moduleTensorRightFunctor (twoChartLine R)
        (tautologicalQuotientLine R)).rightDerivedFunctorPlus.map f.hom := rfl

/-- The FULL connecting square retains original coefficient maps under every derived roof. -/
theorem diagonalPerfectGenerationTriangle_connecting_naturality
    {K L : OriginalPerfectPlus R} (f : K ⟶ L) :
    (diagonalPerfectGenerationTriangle R K).mor₃ ≫
      ((diagonalPerfectGenerationFirstFunctor R).map f.hom)⟦1⟧' =
      (moduleTensorRightFunctor (twoChartLine R)
        (tautologicalQuotientLine R)).rightDerivedFunctorPlus.map f.hom ≫
        (diagonalPerfectGenerationTriangle R L).mor₃ :=
  ((diagonalPerfectGenerationTriangleFunctor R).map f).comm₃
end Quillen.Scheme.ProjectiveLine
