/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.LineTensorAssociator
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalGenerationEndpoints
public import Quillen.Algebra.Homology.DerivedCategory.ExactDerivedContraction

/-! # Actual nested original line contraction

The original determinant pairing, original presheaf/sheafification associator,
original braiding and original units contract L tensor (Q tensor E), or
L tensor (E tensor Q), naturally in arbitrary module sheaves and genuine D+ roofs.
-/
@[expose] public section
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MonoidalCategory AlgebraicGeometry SheafOfModulesOfCommRing
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
local instance originalContractionStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u})

/-- Original tautological line trivializations on the two original polynomial charts. -/
def originalLineChartIso (b : Bool) :
    (tautologicalLine R).restrict (polynomialChart R b) ≅
      SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf := by
  cases b
  · exact tautologicalLineMinusIso R
  · exact tautologicalLinePlusIso R

/-- Original quotient line trivializations on the same original polynomial charts. -/
def originalQuotientChartIso (b : Bool) :
    (tautologicalQuotientLine R).restrict (polynomialChart R b) ≅
      SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf := by
  cases b
  · exact tautologicalQuotientMinusIso R
  · exact tautologicalQuotientPlusIso R

/-- The actual original line associator, using the two original trivialization proofs. -/
def originalLineAssociatorIso :
    moduleTensorLeftFunctor (twoChartLine R) (tautologicalQuotientLine R) ⋙
        moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R) ≅
      moduleTensorLeftFunctor (twoChartLine R)
        ((moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).obj
          (tautologicalQuotientLine R)) :=
  moduleLineTensorAssociator (tautologicalLine R) (tautologicalQuotientLine R)
    (fun _ : Bool => Spec (.of (Polynomial R))) (polynomialChart R)
    (polynomialChart_cover R) (originalLineChartIso R) (originalQuotientChartIso R)

/-- The actual contraction L tensor (Q tensor E) uses the original determinant pairing
and original left unit after the original associator, naturally in E. -/
def originalLeftLineContractionIso :
    moduleTensorLeftFunctor (twoChartLine R) (tautologicalQuotientLine R) ⋙
        moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R) ≅
      𝟭 (twoChartLine R).Modules :=
  originalLineAssociatorIso R ≪≫
    (tensorFunctor (twoChartLine R).sheaf).mapIso (tautologicalLineTensorQuotientIso R) ≪≫
    tensorLeftUnitIso (twoChartLine R).sheaf

/-- Its hom retains the actual determinant map in the original order. -/
theorem originalLeftLineContractionIso_hom (E : (twoChartLine R).Modules) :
    (originalLeftLineContractionIso R).hom.app E =
      (originalLineAssociatorIso R).hom.app E ≫
        (moduleTensorCoefficientMap (twoChartLine R) (tautologicalLinePairing R)).app E ≫
          (tensorLeftUnitIso (twoChartLine R).sheaf).hom.app E := rfl

/-- The actual contraction L tensor (E tensor Q) additionally uses the original braiding. -/
def originalRightLineContractionIso :
    moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R) ⋙
        moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R) ≅
      𝟭 (twoChartLine R).Modules :=
  isoWhiskerRight (moduleTensorSymmetryNatIso (twoChartLine R) (tautologicalQuotientLine R))
      (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)) ≪≫
    originalLeftLineContractionIso R

/-- The actual ORIGINAL nested-left line contraction on every genuine D+ input. -/
def originalDerivedLeftLineContractionIso :
    (moduleTensorLeftFunctor (twoChartLine R)
      (tautologicalQuotientLine R)).rightDerivedFunctorPlus ⋙
        (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).rightDerivedFunctorPlus ≅
      𝟭 (DerivedCategory.Plus (twoChartLine R).Modules) :=
  DerivedCategory.Plus.exactDerivedContractionIso
    (moduleTensorLeftFunctor (twoChartLine R) (tautologicalQuotientLine R))
    (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R))
    (originalLeftLineContractionIso R)

/-- The actual ORIGINAL nested-right line contraction on every genuine D+ input. -/
def originalDerivedRightLineContractionIso :
    (moduleTensorRightFunctor (twoChartLine R)
      (tautologicalQuotientLine R)).rightDerivedFunctorPlus ⋙
        (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).rightDerivedFunctorPlus ≅
      𝟭 (DerivedCategory.Plus (twoChartLine R).Modules) :=
  DerivedCategory.Plus.exactDerivedContractionIso
    (moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R))
    (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R))
    (originalRightLineContractionIso R)

/-- Both installed exact line units and the original determinant contraction are retained. -/
theorem originalDerivedLeftLineContractionIso_unit
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit
      (moduleTensorLeftFunctor (twoChartLine R) (tautologicalQuotientLine R))
      (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R))).app K ≫
        (originalDerivedLeftLineContractionIso R).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (originalLeftLineContractionIso R)).hom.app K ≫
          (Functor.mapCochainComplexPlusIdIso (twoChartLine R).Modules).hom.app K) :=
  DerivedCategory.Plus.exactDerivedContractionIso_unit _ _ _ K

/-- The original braiding, determinant and both installed exact line units are retained. -/
theorem originalDerivedRightLineContractionIso_unit
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit
      (moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R))
      (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R))).app K ≫
        (originalDerivedRightLineContractionIso R).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (originalRightLineContractionIso R)).hom.app K ≫
          (Functor.mapCochainComplexPlusIdIso (twoChartLine R).Modules).hom.app K) :=
  DerivedCategory.Plus.exactDerivedContractionIso_unit _ _ _ K
end AlgebraicGeometry.Scheme.ProjectiveLine
