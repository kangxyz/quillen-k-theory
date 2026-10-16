/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalDerivedVertexComparisons
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DerivedLinePerfectness
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DerivedSelfBaseChangePerfect
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedPerfect

/-! # Genuine original generation endpoints on intrinsic perfect D+

The maps are natural transformations on the actual ambient D+ category. Their
invertibility on the actual perfect full subcategory uses only the ORIGINAL
self-base-change mate; no natural chosen strict representative is involved.
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
local instance perfectGenerationStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u})

/-- Intrinsic perfection on the original bounded-below derived carrier.
This is the literal original perfect predicate on the underlying derived object. -/
abbrev originalPerfectPlusObjects :
    ObjectProperty (DerivedCategory.Plus (twoChartLine R).Modules) :=
  fun K => perfectDerivedObjects (twoChartLine R) K.obj

/-- The actual full subcategory of intrinsic perfect bounded-below derived coefficients. -/
abbrev OriginalPerfectPlus := (originalPerfectPlusObjects R).FullSubcategory

/-- Forget only the intrinsic perfectness proof; original derived roofs remain the morphisms. -/
abbrev originalPerfectPlusInclusion :
    OriginalPerfectPlus R ⥤ DerivedCategory.Plus (twoChartLine R).Modules :=
  (originalPerfectPlusObjects R).ι

/-- The exact original right tautological tensor, K tensor L, in D+. -/
abbrev originalRightLineDerived :
    DerivedCategory.Plus (twoChartLine R).Modules ⥤
      DerivedCategory.Plus (twoChartLine R).Modules :=
  (moduleTensorRightFunctor (twoChartLine R) (tautologicalLine R)).rightDerivedFunctorPlus

/-- The first intended generation endpoint p*Rp*(K tensor L), with original functors. -/
def diagonalPerfectGenerationFirstFunctor :
    DerivedCategory.Plus (twoChartLine R).Modules ⥤
      DerivedCategory.Plus (twoChartLine R).Modules :=
  originalRightLineDerived R ⋙ derivedPushforwardPlus (projection R) ⋙
    derivedFlatPullbackPlus (projection R)

/-- The second intended endpoint Q tensor p*Rp*K, with the original exact left line tensor. -/
def diagonalPerfectGenerationSecondFunctor :
    DerivedCategory.Plus (twoChartLine R).Modules ⥤
      DerivedCategory.Plus (twoChartLine R).Modules :=
  (derivedPushforwardPlus (projection R) ⋙ derivedFlatPullbackPlus (projection R)) ⋙
    (moduleTensorLeftFunctor (twoChartLine R)
      (tautologicalQuotientLine R)).rightDerivedFunctorPlus

/-- The first original coefficient derived functor is computed by original
right line tensor followed by original flat first pullback, through the original mate. -/
def diagonalOriginalFirstTensorPullbackIso :
    originalRightLineDerived R ⋙ derivedFlatPullbackPlus (relativeFirst R) ≅
      (diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₁).rightDerivedFunctorPlus :=
  (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
    (moduleTensorRightFunctor (twoChartLine R) (tautologicalLine R))
      (Scheme.Modules.pullback (relativeFirst R))).symm ≪≫
    (moduleTensorRightFunctor (twoChartLine R) (tautologicalLine R) ⋙
      Scheme.Modules.pullback (relativeFirst R)).rightDerivedFunctorPlusIso
        (tautologicalPullbackTensorNatIso R (relativeFirst R))

/-- The second exact original coefficient functor is computed through the
original derived composition and original sheafified coefficient braiding. -/
def diagonalOriginalSecondTensorPullbackIso :
    derivedFlatPullbackPlus (relativeFirst R) ⋙
        (moduleTensorLeftFunctor (relativeSquare R)
          ((Scheme.Modules.pullback (relativeSecond R)).obj
            (tautologicalQuotientLine R))).rightDerivedFunctorPlus ≅
      (diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₂).rightDerivedFunctorPlus :=
  (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
    (Scheme.Modules.pullback (relativeFirst R))
      (moduleTensorLeftFunctor (relativeSquare R)
        ((Scheme.Modules.pullback (relativeSecond R)).obj
          (tautologicalQuotientLine R)))).symm ≪≫
    (Scheme.Modules.pullback (relativeFirst R) ⋙
      moduleTensorLeftFunctor (relativeSquare R)
        ((Scheme.Modules.pullback (relativeSecond R)).obj
          (tautologicalQuotientLine R))).rightDerivedFunctorPlusIso
      (isoWhiskerLeft (Scheme.Modules.pullback (relativeFirst R))
        (moduleTensorSymmetryNatIso (relativeSquare R)
          ((Scheme.Modules.pullback (relativeSecond R)).obj
            (tautologicalQuotientLine R))).symm)

/-- The ORIGINAL natural first-endpoint comparison. It is defined on all ambient
D+ inputs; only its perfect-input invertibility is asserted. -/
def diagonalPerfectGenerationFirstMap :
    diagonalPerfectGenerationFirstFunctor R ⟶
      diagonalDerivedComplexProjectedTriangleFunctor R ⋙ Triangle.π₁ :=
  whiskerLeft (originalRightLineDerived R) (derivedSelfBaseChangeMap R) ≫
    (associator (originalRightLineDerived R) (derivedFlatPullbackPlus (relativeFirst R))
      (derivedPushforwardPlus (relativeSecond R))).inv ≫
    whiskerRight (diagonalOriginalFirstTensorPullbackIso R).hom
      (derivedPushforwardPlus (relativeSecond R)) ≫
    (diagonalDerivedComplexProjectedFirstIso R).inv

/-- The ORIGINAL natural second-endpoint comparison, with the finite-line
projection formula and installed exact line tensor/derived composition. -/
def diagonalPerfectGenerationSecondMap :
    diagonalPerfectGenerationSecondFunctor R ⟶
      diagonalDerivedComplexProjectedTriangleFunctor R ⋙ Triangle.π₂ :=
  whiskerRight (derivedSelfBaseChangeMap R)
      (moduleTensorLeftFunctor (twoChartLine R)
        (tautologicalQuotientLine R)).rightDerivedFunctorPlus ≫
    (associator (derivedFlatPullbackPlus (relativeFirst R))
      (derivedPushforwardPlus (relativeSecond R))
      (moduleTensorLeftFunctor (twoChartLine R)
        (tautologicalQuotientLine R)).rightDerivedFunctorPlus).hom ≫
    whiskerLeft (derivedFlatPullbackPlus (relativeFirst R))
      (derivedProjectionFormulaIso (relativeSecond R) (tautologicalQuotientLine R)).hom ≫
    (associator (derivedFlatPullbackPlus (relativeFirst R))
      (moduleTensorLeftFunctor (relativeSquare R)
        ((Scheme.Modules.pullback (relativeSecond R)).obj
          (tautologicalQuotientLine R))).rightDerivedFunctorPlus
      (derivedPushforwardPlus (relativeSecond R))).inv ≫
    whiskerRight (diagonalOriginalSecondTensorPullbackIso R).hom
      (derivedPushforwardPlus (relativeSecond R)) ≫
    (diagonalDerivedComplexProjectedSecondIso R).inv

/-- Perfection makes the ORIGINAL first comparison invertible at the actual input. -/
theorem isIso_diagonalPerfectGenerationFirstMap
    (K : DerivedCategory.Plus (twoChartLine R).Modules)
    (hK : perfectDerivedObjects (twoChartLine R) (DerivedCategory.Plus.ι.obj K)) :
    IsIso ((diagonalPerfectGenerationFirstMap R).app K) := by
  let : IsIso ((derivedSelfBaseChangeMap R).app ((originalRightLineDerived R).obj K)) :=
    isIso_derivedSelfBaseChange_perfect R _ (perfect_derivedTautologicalRightTensor R K hK)
  dsimp only [diagonalPerfectGenerationFirstMap, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app]
  infer_instance

/-- Perfection makes the ORIGINAL second comparison invertible at the actual input. -/
theorem isIso_diagonalPerfectGenerationSecondMap
    (K : DerivedCategory.Plus (twoChartLine R).Modules)
    (hK : perfectDerivedObjects (twoChartLine R) (DerivedCategory.Plus.ι.obj K)) :
    IsIso ((diagonalPerfectGenerationSecondMap R).app K) := by
  let : IsIso ((derivedSelfBaseChangeMap R).app K) :=
    isIso_derivedSelfBaseChange_perfect R K hK
  dsimp only [diagonalPerfectGenerationSecondMap, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app]
  infer_instance

/-- The first generation comparison is an original natural isomorphism on the
actual intrinsic-perfect D+ full subcategory, with canonical inverse. -/
def diagonalPerfectGenerationFirstIso :
    originalPerfectPlusInclusion R ⋙ diagonalPerfectGenerationFirstFunctor R ≅
      originalPerfectPlusInclusion R ⋙
        diagonalDerivedComplexProjectedTriangleFunctor R ⋙ Triangle.π₁ := by
  let α := whiskerLeft (originalPerfectPlusInclusion R) (diagonalPerfectGenerationFirstMap R)
  have hα : IsIso α := by
    apply (NatTrans.isIso_iff_isIso_app α).mpr
    intro K
    exact isIso_diagonalPerfectGenerationFirstMap R K.obj K.property
  exact asIso α

/-- The second generation comparison is an original natural isomorphism on the
actual intrinsic-perfect D+ full subcategory, with canonical inverse. -/
def diagonalPerfectGenerationSecondIso :
    originalPerfectPlusInclusion R ⋙ diagonalPerfectGenerationSecondFunctor R ≅
      originalPerfectPlusInclusion R ⋙
        diagonalDerivedComplexProjectedTriangleFunctor R ⋙ Triangle.π₂ := by
  let α := whiskerLeft (originalPerfectPlusInclusion R) (diagonalPerfectGenerationSecondMap R)
  have hα : IsIso α := by
    apply (NatTrans.isIso_iff_isIso_app α).mpr
    intro K
    exact isIso_diagonalPerfectGenerationSecondMap R K.obj K.property
  exact asIso α
end AlgebraicGeometry.Scheme.ProjectiveLine
