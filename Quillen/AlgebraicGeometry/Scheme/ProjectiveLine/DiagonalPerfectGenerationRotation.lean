/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalPerfectGenerationTriangle
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.OriginalLineContraction

/-! # Natural original signed rotation giving p*G0(K) to K to L tensor p*G1(K)

Tensor the FULL original generation triangle by the exact original left line L,
rotate once with the original negative shifted incidence, and contract its
specified nested lines through original determinant, associator, unit and braiding maps.
-/
@[expose] public section

open AlgebraicGeometry
open CategoryTheory.Pretriangulated

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
local instance perfectRotationStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u})

/-- The original exact left tensor by L in the actual D+ category. -/
abbrev originalLeftLineDerived :=
  (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).rightDerivedFunctorPlus

/-- The original coefficient G0(K)=Rp*K on the intrinsic perfect D+ carrier. -/
def diagonalGenerationG0 : OriginalPerfectPlus R ⥤ DerivedCategory.Plus (Spec R).Modules :=
  originalPerfectPlusInclusion R ⋙ derivedPushforwardPlus (projection R)

/-- The original coefficient G1(K)=Rp*(K tensor L)[1], with the specified shift. -/
def diagonalGenerationG1 : OriginalPerfectPlus R ⥤ DerivedCategory.Plus (Spec R).Modules :=
  originalPerfectPlusInclusion R ⋙ originalRightLineDerived R ⋙
    derivedPushforwardPlus (projection R) ⋙
      shiftFunctor (DerivedCategory.Plus (Spec R).Modules) (1 : ℤ)

/-- The first final vertex is literally p*G0(K). -/
def diagonalRotatedGenerationFirst :
    OriginalPerfectPlus R ⥤ DerivedCategory.Plus (twoChartLine R).Modules :=
  diagonalGenerationG0 R ⋙ derivedFlatPullbackPlus (projection R)

/-- The third final vertex is literally L tensor p*G1(K), in the original order. -/
def diagonalRotatedGenerationThird :
    OriginalPerfectPlus R ⥤ DerivedCategory.Plus (twoChartLine R).Modules :=
  diagonalGenerationG1 R ⋙ derivedFlatPullbackPlus (projection R) ⋙ originalLeftLineDerived R

/-- Apply exact original L tensor, then rotate the FULL original triangle once. -/
def diagonalOriginalLineRotatedFunctor :
    OriginalPerfectPlus R ⥤ Triangle (DerivedCategory.Plus (twoChartLine R).Modules) :=
  diagonalPerfectGenerationTriangleFunctor R ⋙ (originalLeftLineDerived R).mapTriangle ⋙
    CategoryTheory.Pretriangulated.rotate _

/-- The original nested-left determinant contraction
identifies p*G0(K) with the raw first vertex. -/
def diagonalRotatedFirstIso :
    diagonalRotatedGenerationFirst R ≅ diagonalOriginalLineRotatedFunctor R ⋙ Triangle.π₁ :=
  NatIso.ofComponents
    (fun K => ((originalDerivedLeftLineContractionIso R).app
      ((diagonalRotatedGenerationFirst R).obj K)).symm)
    (fun f => (originalDerivedLeftLineContractionIso R).inv.naturality
      ((diagonalRotatedGenerationFirst R).map f))

/-- The original braiding/determinant contraction identifies K with the raw middle vertex. -/
def diagonalRotatedMiddleIso :
    originalPerfectPlusInclusion R ≅ diagonalOriginalLineRotatedFunctor R ⋙ Triangle.π₂ :=
  NatIso.ofComponents (fun K => ((originalDerivedRightLineContractionIso R).app K.obj).symm)
    (fun f => (originalDerivedRightLineContractionIso R).inv.naturality f.hom)

/-- The original exact pullback/line shift comparison identifies L tensor p*G1(K)
with the raw third rotated vertex, with the original order and shift. -/
def diagonalRotatedThirdIso :
    diagonalRotatedGenerationThird R ≅ diagonalOriginalLineRotatedFunctor R ⋙ Triangle.π₃ :=
  NatIso.ofComponents
    (fun K => (Functor.commShiftIso
      (derivedFlatPullbackPlus (projection R) ⋙ originalLeftLineDerived R) (1 : ℤ)).app
        ((derivedPushforwardPlus (projection R)).obj ((originalRightLineDerived R).obj K.obj)))
    (fun f => (Functor.commShiftIso
      (derivedFlatPullbackPlus (projection R) ⋙ originalLeftLineDerived R) (1 : ℤ)).hom.naturality
        ((derivedPushforwardPlus (projection R)).map ((originalRightLineDerived R).map f.hom)))

/-- The actual natural triangle p*G0(K) to K to L tensor p*G1(K), with original maps. -/
def diagonalRotatedGenerationTriangleFunctor :
    OriginalPerfectPlus R ⥤ Triangle (DerivedCategory.Plus (twoChartLine R).Modules) :=
  Quillen.TriangleTransport.functor (diagonalOriginalLineRotatedFunctor R)
    (diagonalRotatedFirstIso R) (diagonalRotatedMiddleIso R) (diagonalRotatedThirdIso R)

/-- The final triangle retains the actual exact-L tensor and signed original rotation. -/
def diagonalRotatedGenerationToOriginalIso :
    diagonalRotatedGenerationTriangleFunctor R ≅ diagonalOriginalLineRotatedFunctor R :=
  Quillen.TriangleTransport.iso (diagonalOriginalLineRotatedFunctor R)
    (diagonalRotatedFirstIso R) (diagonalRotatedMiddleIso R) (diagonalRotatedThirdIso R)

/-- The final actual generation triangle at the original intrinsic-perfect derived object. -/
abbrev diagonalRotatedGenerationTriangle (K : OriginalPerfectPlus R) :=
  (diagonalRotatedGenerationTriangleFunctor R).obj K

/-- Every final intrinsic-perfect generation triangle is distinguished. -/
theorem diagonalRotatedGenerationTriangle_distinguished (K : OriginalPerfectPlus R) :
    diagonalRotatedGenerationTriangle R K ∈
      distTriang (DerivedCategory.Plus (twoChartLine R).Modules) := by
  have ht := (originalLeftLineDerived R).map_distinguished _
    (diagonalPerfectGenerationTriangle_distinguished R K)
  exact isomorphic_distinguished _ (rot_of_distTriang _ ht) _
    ((diagonalRotatedGenerationToOriginalIso R).app K)

/-- The first final map is exactly the original p*G0 map, under every genuine derived roof. -/
@[simp] theorem diagonalRotatedGenerationTriangleMap_hom₁
    {K L : OriginalPerfectPlus R} (f : K ⟶ L) :
    ((diagonalRotatedGenerationTriangleFunctor R).map f).hom₁ =
      (diagonalRotatedGenerationFirst R).map f := rfl

/-- The middle final map is exactly the original derived coefficient morphism. -/
@[simp] theorem diagonalRotatedGenerationTriangleMap_hom₂
    {K L : OriginalPerfectPlus R} (f : K ⟶ L) :
    ((diagonalRotatedGenerationTriangleFunctor R).map f).hom₂ = f.hom := rfl

/-- The third final map is exactly the original L tensor p*G1 map under every derived roof. -/
@[simp] theorem diagonalRotatedGenerationTriangleMap_hom₃
    {K L : OriginalPerfectPlus R} (f : K ⟶ L) :
    ((diagonalRotatedGenerationTriangleFunctor R).map f).hom₃ =
      (diagonalRotatedGenerationThird R).map f := rfl

/-- The first final arrow retains the ORIGINAL exact-L image of the quotient arrow. -/
theorem diagonalRotatedGenerationTriangle_mor₁ (K : OriginalPerfectPlus R) :
    (diagonalRotatedGenerationTriangle R K).mor₁ =
      (diagonalRotatedFirstIso R).hom.app K ≫
        (originalLeftLineDerived R).map ((diagonalPerfectGenerationQuotient R).app K) ≫
        (diagonalRotatedMiddleIso R).inv.app K := rfl

/-- The second final arrow retains the ORIGINAL connecting map and installed exact-L shift unit. -/
theorem diagonalRotatedGenerationTriangle_mor₂ (K : OriginalPerfectPlus R) :
    (diagonalRotatedGenerationTriangle R K).mor₂ =
      (diagonalRotatedMiddleIso R).hom.app K ≫
        ((originalLeftLineDerived R).map ((diagonalPerfectGenerationConnecting R).app K) ≫
          ((originalLeftLineDerived R).commShiftIso (1 : ℤ)).hom.app
            ((diagonalPerfectGenerationFirstFunctor R).obj K.obj)) ≫
        (diagonalRotatedThirdIso R).inv.app K := rfl

/-- The final connecting arrow retains the ORIGINAL negative shifted incidence. -/
theorem diagonalRotatedGenerationTriangle_mor₃ (K : OriginalPerfectPlus R) :
    (diagonalRotatedGenerationTriangle R K).mor₃ =
      (diagonalRotatedThirdIso R).hom.app K ≫
        (-((originalLeftLineDerived R).map
          ((diagonalPerfectGenerationIncidence R).app K))⟦1⟧') ≫
        ((diagonalRotatedFirstIso R).inv.app K)⟦1⟧' := rfl

/-- The final connecting square retains the original G0/G1 maps under every derived roof. -/
theorem diagonalRotatedGenerationTriangle_connecting_naturality
    {K L : OriginalPerfectPlus R} (f : K ⟶ L) :
    (diagonalRotatedGenerationTriangle R K).mor₃ ≫
      ((diagonalRotatedGenerationFirst R).map f)⟦1⟧' =
    (diagonalRotatedGenerationThird R).map f ≫
      (diagonalRotatedGenerationTriangle R L).mor₃ :=
  ((diagonalRotatedGenerationTriangleFunctor R).map f).comm₃
end AlgebraicGeometry.Scheme.ProjectiveLine
