/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalPerfectGenerationEndpoints

/-! # Actual original unit equations for the generation endpoint comparisons -/
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
local instance generationUnitStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u})

/-- The first comparison retains the literal original pullback/tensor mate
and both installed exact coefficient derived units. -/
theorem diagonalOriginalFirstTensorPullbackIso_unit
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit
      (moduleTensorRightFunctor (twoChartLine R) (tautologicalLine R))
      (Scheme.Modules.pullback (relativeFirst R))).app K ≫
        (diagonalOriginalFirstTensorPullbackIso R).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus
          (tautologicalPullbackTensorNatIso R (relativeFirst R))).hom.app K) ≫
        (diagonalCoefficientFunctor R
          (diagonalIncidenceSequence R).X₁).rightDerivedFunctorPlusUnit.app K := by
  let F := moduleTensorRightFunctor (twoChartLine R) (tautologicalLine R)
  let G := Scheme.Modules.pullback (relativeFirst R)
  have hC := F.rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app G K
  rw [← Functor.rightDerivedFunctorPlusCompUnit_app F G K] at hC
  have hE := (F ⋙ G).rightDerivedFunctorPlusIso_hom_app
    (tautologicalPullbackTensorNatIso R (relativeFirst R)) K
  rw [← hC]
  change (_ ≫ _) ≫ (_ ≫ _) = _
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]
  exact hE

/-- The second comparison retains the original sheafified braiding
and both installed exact pullback/line derived units. -/
theorem diagonalOriginalSecondTensorPullbackIso_unit
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit
      (Scheme.Modules.pullback (relativeFirst R))
      (moduleTensorLeftFunctor (relativeSquare R)
        ((Scheme.Modules.pullback (relativeSecond R)).obj
          (tautologicalQuotientLine R)))).app K ≫
        (diagonalOriginalSecondTensorPullbackIso R).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus
          (isoWhiskerLeft (Scheme.Modules.pullback (relativeFirst R))
            (moduleTensorSymmetryNatIso (relativeSquare R)
              ((Scheme.Modules.pullback (relativeSecond R)).obj
                (tautologicalQuotientLine R))).symm)).hom.app K) ≫
        (diagonalCoefficientFunctor R
          (diagonalIncidenceSequence R).X₂).rightDerivedFunctorPlusUnit.app K := by
  let F := Scheme.Modules.pullback (relativeFirst R)
  let G := moduleTensorLeftFunctor (relativeSquare R)
    ((Scheme.Modules.pullback (relativeSecond R)).obj (tautologicalQuotientLine R))
  have hC := F.rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app G K
  rw [← Functor.rightDerivedFunctorPlusCompUnit_app F G K] at hC
  have hE := (F ⋙ G).rightDerivedFunctorPlusIso_hom_app
    (isoWhiskerLeft F (moduleTensorSymmetryNatIso (relativeSquare R)
      ((Scheme.Modules.pullback (relativeSecond R)).obj (tautologicalQuotientLine R))).symm) K
  rw [← hC]
  change (_ ≫ _) ≫ (_ ≫ _) = _
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]
  exact hE

/-- The first entire endpoint map is the ORIGINAL base-change mate, original
pullback/tensor comparison, and original localization/derived unit inverse. -/
theorem diagonalPerfectGenerationFirstMap_app
    (K : DerivedCategory.Plus (twoChartLine R).Modules) :
    (diagonalPerfectGenerationFirstMap R).app K =
      (derivedSelfBaseChangeMap R).app ((originalRightLineDerived R).obj K) ≫
        (derivedPushforwardPlus (relativeSecond R)).map
          ((diagonalOriginalFirstTensorPullbackIso R).hom.app K) ≫
        (diagonalDerivedComplexProjectedFirstIso R).inv.app K := by
  dsimp [diagonalPerfectGenerationFirstMap]
  erw [Category.id_comp]

/-- The second entire endpoint map retains the ORIGINAL base-change mate,
finite-line projection formula, original braiding and installed exact units. -/
theorem diagonalPerfectGenerationSecondMap_app
    (K : DerivedCategory.Plus (twoChartLine R).Modules) :
    (diagonalPerfectGenerationSecondMap R).app K =
      (moduleTensorLeftFunctor (twoChartLine R)
        (tautologicalQuotientLine R)).rightDerivedFunctorPlus.map
          ((derivedSelfBaseChangeMap R).app K) ≫
        (derivedProjectionFormulaIso (relativeSecond R) (tautologicalQuotientLine R)).hom.app
          ((derivedFlatPullbackPlus (relativeFirst R)).obj K) ≫
        (derivedPushforwardPlus (relativeSecond R)).map
          ((diagonalOriginalSecondTensorPullbackIso R).hom.app K) ≫
        (diagonalDerivedComplexProjectedSecondIso R).inv.app K := by
  dsimp [diagonalPerfectGenerationSecondMap]
  simp only [Category.id_comp]
end AlgebraicGeometry.Scheme.ProjectiveLine
