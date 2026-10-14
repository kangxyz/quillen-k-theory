/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalComplexTensorTriangle
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalProjectedTensorTriangle

/-! # Original all-coefficient complex triangle after derived second projection

The third vertex is identified through the original all-coefficient closed
projection formula, the exact closed-pushforward unit, the exact line-tensor
unit, and the original geometric derived section comparison. These are natural
isomorphisms on genuine D+ inputs and morphisms, without strict perfect models.
The first two projected terms remain their actual derived-image objects.
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
local instance diagonalComplexProjectedStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
local instance diagonalComplexProjectedClosed (R : CommRingCat.{u}) :
    IsClosedImmersion (relativeDiagonal R) := isClosedImmersion_relativeDiagonal R
variable (R : CommRingCat.{u})

/-- The third raw triangle functor is exactly the original third coefficient complex functor. -/
def diagonalComplexThirdFunctorIso :
    diagonalComplexTensorTriangleFunctor R ⋙ Triangle.π₃ ≅
      (diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₃).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    dsimp
    rw [Category.comp_id, Category.id_comp]
    exact diagonalComplexTensorTriangleMap_hom₃ R f)

/-- The actual complex-level third identification uses the original projection arrow
and the installed exact closed-pushforward unit. -/
def diagonalComplexClosedVertexIso :
    diagonalComplexTensorTriangleFunctor R ⋙ Triangle.π₃ ≅
      (moduleTensorRightFunctor (twoChartLine R)
        (tautologicalQuotientLine R)).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus (relativeDiagonal R) := by
  let T := moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R)
  let J := Scheme.Modules.pushforward (relativeDiagonal R)
  let := J.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  exact diagonalComplexThirdFunctorIso R ≪≫
    isoWhiskerRight (NatIso.mapCochainComplexPlus (diagonalCoefficientThirdIso R) ≪≫
      T.mapCochainComplexPlusCompIso J) DerivedCategory.Plus.Q ≪≫
    associator T.mapCochainComplexPlus J.mapCochainComplexPlus DerivedCategory.Plus.Q ≪≫
    isoWhiskerLeft T.mapCochainComplexPlus (asIso J.rightDerivedFunctorPlusUnit)

/-- The complex-level comparison retains each original coefficient projection-formula
map, followed by the installed derived closed-pushforward unit. -/
theorem diagonalComplexClosedVertexIso_hom
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    (diagonalComplexClosedVertexIso R).hom.app K =
      DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (diagonalCoefficientThirdIso R)).hom.app K ≫
          (Functor.mapCochainComplexPlusCompIso
            (moduleTensorRightFunctor (twoChartLine R)
        (tautologicalQuotientLine R))
            (Scheme.Modules.pushforward (relativeDiagonal R))).hom.app K) ≫
        (derivedPushforwardPlusUnit (relativeDiagonal R)).app
          ((moduleTensorRightFunctor (twoChartLine R)
            (tautologicalQuotientLine R)).mapCochainComplexPlus.obj K) := by
  simp [diagonalComplexClosedVertexIso, diagonalComplexThirdFunctorIso,
    Functor.mapCochainComplexPlusCompIso]
  rfl

/-- A genuine D+ natural identification of the original third vertex with
R(diagonal pushforward) of the exact original quotient-line tensor. -/
def diagonalDerivedComplexThirdIso :
    diagonalDerivedComplexTriangleFunctor R ⋙ Triangle.π₃ ≅
      (moduleTensorRightFunctor (twoChartLine R)
        (tautologicalQuotientLine R)).rightDerivedFunctorPlus ⋙
        derivedPushforwardPlus (relativeDiagonal R) := by
  let T := moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R)
  let := T.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (twoChartLine R).Modules)
    (DerivedCategory.Plus (relativeSquare R).Modules)).preimageIso
  exact (associator DerivedCategory.Plus.Q (diagonalDerivedComplexTriangleFunctor R)
      Triangle.π₃).symm ≪≫
    isoWhiskerRight (diagonalDerivedComplexTriangleFactors R) Triangle.π₃ ≪≫
    diagonalComplexClosedVertexIso R ≪≫
    (associator T.mapCochainComplexPlus DerivedCategory.Plus.Q
      (derivedPushforwardPlus (relativeDiagonal R))).symm ≪≫
    isoWhiskerRight (asIso T.rightDerivedFunctorPlusUnit)
      (derivedPushforwardPlus (relativeDiagonal R)) ≪≫
    associator DerivedCategory.Plus.Q T.rightDerivedFunctorPlus
      (derivedPushforwardPlus (relativeDiagonal R))

/-- The D+ third identification retains the actual triangle factor and both
installed exact derived units on every original coefficient complex. -/
theorem diagonalDerivedComplexThirdIso_factors
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    (diagonalDerivedComplexThirdIso R).hom.app (DerivedCategory.Plus.Q.obj K) =
      ((diagonalDerivedComplexTriangleFactors R).hom.app K).hom₃ ≫
        (diagonalComplexClosedVertexIso R).hom.app K ≫
          (derivedPushforwardPlus (relativeDiagonal R)).map
            ((moduleTensorRightFunctor (twoChartLine R)
              (tautologicalQuotientLine R)).rightDerivedFunctorPlusUnit.app K) := by
  let T := moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R)
  let := T.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let e : DerivedCategory.Plus.Q ⋙
      (diagonalDerivedComplexTriangleFunctor R ⋙ Triangle.π₃) ≅
      DerivedCategory.Plus.Q ⋙ (T.rightDerivedFunctorPlus ⋙
        derivedPushforwardPlus (relativeDiagonal R)) :=
    (associator DerivedCategory.Plus.Q (diagonalDerivedComplexTriangleFunctor R)
      Triangle.π₃).symm ≪≫
    isoWhiskerRight (diagonalDerivedComplexTriangleFactors R) Triangle.π₃ ≪≫
    diagonalComplexClosedVertexIso R ≪≫
    (associator T.mapCochainComplexPlus DerivedCategory.Plus.Q
      (derivedPushforwardPlus (relativeDiagonal R))).symm ≪≫
    isoWhiskerRight (asIso T.rightDerivedFunctorPlusUnit)
      (derivedPushforwardPlus (relativeDiagonal R)) ≪≫
    associator DerivedCategory.Plus.Q T.rightDerivedFunctorPlus
      (derivedPushforwardPlus (relativeDiagonal R))
  have he := congrArg (fun α => α.app K)
    ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Q
      (CochainComplex.Plus.quasiIso (twoChartLine R).Modules)
      (DerivedCategory.Plus (relativeSquare R).Modules)).map_preimage e.hom)
  change (diagonalDerivedComplexThirdIso R).hom.app (DerivedCategory.Plus.Q.obj K) =
    e.hom.app K at he
  rw [he]
  dsimp [e]
  simp only [Category.id_comp, Category.comp_id]
  erw [Category.id_comp]

/-- Apply the original second-projection derived functor to the descended original triangle. -/
def diagonalDerivedComplexProjectedTriangleFunctor :
    DerivedCategory.Plus (twoChartLine R).Modules ⥤
      Triangle (DerivedCategory.Plus (twoChartLine R).Modules) :=
  diagonalDerivedComplexTriangleFunctor R ⋙ (derivedPushforwardPlus (relativeSecond R)).mapTriangle

/-- The actual derived second projection preserves distinguishedness for every D+ input. -/
theorem diagonalDerivedComplexProjectedTriangle_distinguished
    (K : DerivedCategory.Plus (twoChartLine R).Modules) :
    (diagonalDerivedComplexProjectedTriangleFunctor R).obj K ∈
      distTriang (DerivedCategory.Plus (twoChartLine R).Modules) :=
  (derivedPushforwardPlus (relativeSecond R)).map_distinguished _
    (diagonalDerivedComplexTriangle_distinguished R K)

/-- The genuine original closed projection/section composite identifies the projected
third vertex with the exact original coefficient tensor by Q, naturally on all D+ morphisms. -/
def diagonalDerivedComplexProjectedVertexIso :
    diagonalDerivedComplexProjectedTriangleFunctor R ⋙ Triangle.π₃ ≅
      (moduleTensorRightFunctor (twoChartLine R)
        (tautologicalQuotientLine R)).rightDerivedFunctorPlus :=
  (associator (diagonalDerivedComplexTriangleFunctor R) Triangle.π₃
      (derivedPushforwardPlus (relativeSecond R))).symm ≪≫
    isoWhiskerRight (diagonalDerivedComplexThirdIso R)
      (derivedPushforwardPlus (relativeSecond R)) ≪≫
    associator
      (moduleTensorRightFunctor (twoChartLine R)
        (tautologicalQuotientLine R)).rightDerivedFunctorPlus
      (derivedPushforwardPlus (relativeDiagonal R)) (derivedPushforwardPlus (relativeSecond R)) ≪≫
    isoWhiskerLeft
      (moduleTensorRightFunctor (twoChartLine R)
        (tautologicalQuotientLine R)).rightDerivedFunctorPlus
      (derivedDiagonalSecondIso R) ≪≫
    rightUnitor _

/-- The projected vertex comparison retains the actual derived diagonal/second
section composite in its original order. -/
theorem diagonalDerivedComplexProjectedVertexIso_hom
    (K : DerivedCategory.Plus (twoChartLine R).Modules) :
    (diagonalDerivedComplexProjectedVertexIso R).hom.app K =
      (derivedPushforwardPlus (relativeSecond R)).map
        ((diagonalDerivedComplexThirdIso R).hom.app K) ≫
      (derivedDiagonalSecondIso R).hom.app
        ((moduleTensorRightFunctor (twoChartLine R)
          (tautologicalQuotientLine R)).rightDerivedFunctorPlus.obj K) := by
  dsimp [diagonalDerivedComplexProjectedVertexIso]
  simp only [Category.id_comp, Category.comp_id]
  erw [Category.id_comp]

/-- Every derived coefficient morphism, hence every genuine roof, respects the
original closed projection/section comparison. -/
@[reassoc] theorem diagonalDerivedComplexProjectedVertexIso_naturality
    {K L : DerivedCategory.Plus (twoChartLine R).Modules} (f : K ⟶ L) :
    ((diagonalDerivedComplexProjectedTriangleFunctor R).map f).hom₃ ≫
      (diagonalDerivedComplexProjectedVertexIso R).hom.app L =
    (diagonalDerivedComplexProjectedVertexIso R).hom.app K ≫
      (moduleTensorRightFunctor (twoChartLine R)
        (tautologicalQuotientLine R)).rightDerivedFunctorPlus.map f :=
  (diagonalDerivedComplexProjectedVertexIso R).hom.naturality f
/-- The actual original projected triangle with its naturally identified coefficient tensor term. -/
def diagonalDerivedComplexCoefficientTriangle
    (K : DerivedCategory.Plus (twoChartLine R).Modules) :
    Triangle (DerivedCategory.Plus (twoChartLine R).Modules) :=
  Triangle.mk ((diagonalDerivedComplexProjectedTriangleFunctor R).obj K).mor₁
    (((diagonalDerivedComplexProjectedTriangleFunctor R).obj K).mor₂ ≫
      (diagonalDerivedComplexProjectedVertexIso R).hom.app K)
    ((diagonalDerivedComplexProjectedVertexIso R).inv.app K ≫
      ((diagonalDerivedComplexProjectedTriangleFunctor R).obj K).mor₃)

/-- The coefficient identification retains the original first two vertices and
original quotient and connecting arrows under the displayed natural isomorphism. -/
def diagonalDerivedComplexCoefficientTriangleIso
    (K : DerivedCategory.Plus (twoChartLine R).Modules) :
    diagonalDerivedComplexCoefficientTriangle R K ≅
      (diagonalDerivedComplexProjectedTriangleFunctor R).obj K := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((diagonalDerivedComplexProjectedVertexIso R).app K).symm ?_ ?_ ?_
  all_goals dsimp [diagonalDerivedComplexCoefficientTriangle]; simp

/-- Transport of the actual original derived maps makes the identified coefficient
triangles into a functor on genuine D+ objects and roofs. -/
def diagonalDerivedComplexCoefficientTriangleFunctor :
    DerivedCategory.Plus (twoChartLine R).Modules ⥤
      Triangle (DerivedCategory.Plus (twoChartLine R).Modules) where
  obj K := diagonalDerivedComplexCoefficientTriangle R K
  map {K L} f := (diagonalDerivedComplexCoefficientTriangleIso R K).hom ≫
    (diagonalDerivedComplexProjectedTriangleFunctor R).map f ≫
      (diagonalDerivedComplexCoefficientTriangleIso R L).inv
  map_id K := by
    rw [(diagonalDerivedComplexProjectedTriangleFunctor R).map_id,
      Category.id_comp, Iso.hom_inv_id]
  map_comp {K L M} f g := by
    rw [(diagonalDerivedComplexProjectedTriangleFunctor R).map_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Every identified coefficient triangle is distinguished for every intrinsic D+ input. -/
theorem diagonalDerivedComplexCoefficientTriangle_distinguished
    (K : DerivedCategory.Plus (twoChartLine R).Modules) :
    diagonalDerivedComplexCoefficientTriangle R K ∈
      distTriang (DerivedCategory.Plus (twoChartLine R).Modules) :=
  isomorphic_distinguished _ (diagonalDerivedComplexProjectedTriangle_distinguished R K) _
    (diagonalDerivedComplexCoefficientTriangleIso R K)

/-- The transported third map is exactly the original derived quotient-line coefficient map. -/
@[simp] theorem diagonalDerivedComplexCoefficientTriangleMap_hom₃
    {K L : DerivedCategory.Plus (twoChartLine R).Modules} (f : K ⟶ L) :
    ((diagonalDerivedComplexCoefficientTriangleFunctor R).map f).hom₃ =
      (moduleTensorRightFunctor (twoChartLine R)
        (tautologicalQuotientLine R)).rightDerivedFunctorPlus.map f := by
  change (diagonalDerivedComplexProjectedVertexIso R).inv.app K ≫
    ((diagonalDerivedComplexProjectedTriangleFunctor R).map f).hom₃ ≫
      (diagonalDerivedComplexProjectedVertexIso R).hom.app L = _
  rw [diagonalDerivedComplexProjectedVertexIso_naturality, Iso.inv_hom_id_app_assoc]

/-- The canonical identified-coefficient connecting square holds for all genuine
D+ morphisms with the original quotient-line coefficient map. -/
theorem diagonalDerivedComplexCoefficientTriangle_connecting_naturality
    {K L : DerivedCategory.Plus (twoChartLine R).Modules} (f : K ⟶ L) :
    (diagonalDerivedComplexCoefficientTriangle R K).mor₃ ≫
      (((diagonalDerivedComplexCoefficientTriangleFunctor R).map f).hom₁)⟦1⟧' =
      (moduleTensorRightFunctor (twoChartLine R)
        (tautologicalQuotientLine R)).rightDerivedFunctorPlus.map f ≫
        (diagonalDerivedComplexCoefficientTriangle R L).mor₃ := by
  have h := ((diagonalDerivedComplexCoefficientTriangleFunctor R).map f).comm₃
  rw [diagonalDerivedComplexCoefficientTriangleMap_hom₃] at h
  exact h

end Quillen.Scheme.ProjectiveLine
