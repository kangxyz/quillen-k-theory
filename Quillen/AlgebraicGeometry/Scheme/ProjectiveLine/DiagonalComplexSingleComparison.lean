/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalComplexTensorTriangle
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalGenerationNaturality

/-! # Correspondence with the original vector-bundle single triangle

The actual termwise single comparison identifies short exact sequences. Mapping
that original sequence isomorphism through Mathlib's canonical SES triangle,
then through the fully faithful D+ inclusion, identifies the whole triangle,
including its original connecting arrow and cone sign.
-/

@[expose] public section
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
local instance diagonalComplexSingleStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u})

/-- The actual single comparison is natural in the original sequence arrow. -/
theorem diagonalCoefficientSingle_comm
    {A B : (relativeSquare R).Modules} (g : A ⟶ B) (E : (twoChartLine R).Modules) :
    (HomologicalComplex.singleMapHomologicalComplex (diagonalCoefficientFunctor R A)
      (.up ℤ) 0).hom.app E ≫
      (HomologicalComplex.single (relativeSquare R).Modules (.up ℤ) 0).map
        ((diagonalCoefficientMap R g).app E) =
    ((diagonalCoefficientMap R g).mapHomologicalComplex (.up ℤ)).app
        ((HomologicalComplex.single (twoChartLine R).Modules (.up ℤ) 0).obj E) ≫
      (HomologicalComplex.singleMapHomologicalComplex (diagonalCoefficientFunctor R B)
        (.up ℤ) 0).hom.app E := by
  rw [HomologicalComplex.natTransMapHomologicalComplex_app_single_obj]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

/-- The termwise diagonal complex at a single coefficient is the original sheaf
sequence placed in degree zero, using the original functor single comparisons. -/
def diagonalComplexSingleSequenceIso (E : (twoChartLine R).Modules) :
    (((diagonalComplexSequenceFunctor R).obj (singleZeroPlus (twoChartLine R) E)).map
      (CochainComplex.Plus.ι (relativeSquare R).Modules)) ≅
      (diagonalBundleTensorSequence R E).map
        (HomologicalComplex.single (relativeSquare R).Modules (.up ℤ) 0) :=
  ShortComplex.isoMk
    ((HomologicalComplex.singleMapHomologicalComplex
      (diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₁) (.up ℤ) 0).app E)
    ((HomologicalComplex.singleMapHomologicalComplex
      (diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₂) (.up ℤ) 0).app E)
    ((HomologicalComplex.singleMapHomologicalComplex
      (diagonalCoefficientFunctor R (diagonalIncidenceSequence R).X₃) (.up ℤ) 0).app E)
    (diagonalCoefficientSingle_comm R (diagonalIncidence R) E)
    (diagonalCoefficientSingle_comm R (diagonalQuotientMap R) E)

/-- The canonical full derived triangle isomorphism at a vector-bundle single
comes from the actual original short-exact sequence isomorphism. -/
def diagonalComplexSingleFullTriangleIso (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] :
    DerivedCategory.Plus.ι.mapTriangle.obj
      ((diagonalComplexTensorTriangleFunctor R).obj (singleZeroPlus (twoChartLine R) E)) ≅
      (diagonalBundleTensorSequence_shortExact R E).singleTriangle := by
  let h₁ := diagonalComplexSequence_shortExact R (singleZeroPlus (twoChartLine R) E)
  let h₂ := (diagonalBundleTensorSequence_shortExact R E).map_of_exact
    (HomologicalComplex.single (relativeSquare R).Modules (.up ℤ) 0)
  let e := diagonalComplexSingleSequenceIso R E
  let m := DerivedCategory.triangleOfSES.map h₁ h₂ e.hom
  have hm : IsIso m := by
    apply Triangle.isIso_of_isIsos
    · dsimp [m, DerivedCategory.triangleOfSES.map]
      infer_instance
    · dsimp [m, DerivedCategory.triangleOfSES.map]
      infer_instance
    · dsimp [m, DerivedCategory.triangleOfSES.map]
      infer_instance
  exact DerivedCategory.Plus.triangleOfSESPlusιIso h₁ ≪≫ asIso m ≪≫
    (CategoryTheory.ShortComplex.ShortExact.singleTriangleIso
      (diagonalBundleTensorSequence_shortExact R E)).symm

/-- The entire new actual complex triangle recovers the maintained original
vector-bundle single triangle, including the incidence, quotient and connecting arrows. -/
def diagonalComplexSingleTriangleIso (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] :
    (diagonalComplexTensorTriangleFunctor R).obj (singleZeroPlus (twoChartLine R) E) ≅
      diagonalBundleTensorTrianglePlus R E :=
  DerivedCategory.Plus.ι.mapTriangle.preimageIso
    (diagonalComplexSingleFullTriangleIso R E ≪≫
      (diagonalBundleTensorSequence_shortExact R E).singleTrianglePlusιIso.symm)

/-- Localization at the original single input retains the same original triangle correspondence. -/
def diagonalDerivedComplexSingleTriangleIso (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] :
    (diagonalDerivedComplexTriangleFunctor R).obj
      (DerivedCategory.Plus.Q.obj (singleZeroPlus (twoChartLine R) E)) ≅
      diagonalBundleTensorTrianglePlus R E :=
  (diagonalDerivedComplexTriangleFactors R).app (singleZeroPlus (twoChartLine R) E) ≪≫
    diagonalComplexSingleTriangleIso R E
end AlgebraicGeometry.Scheme.ProjectiveLine
