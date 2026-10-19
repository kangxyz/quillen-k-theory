/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationStableComparison

/-!
# The actual exact inverse of normalized global evaluation

This is the existing categorical evaluation inverse with its prescribed chosen-zero
normalization. The original categorical unit and counit remain explicit; no inverse
in a stable localization is selected.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- The original categorical inverse, normalized only at the chosen zero. -/
def evaluationInverseModel (X : Scheme.{u}ᵒᵖ) :
    modelOf (boundedFlatPerfectWaldhausen X.unop) ⟶ globalModel.obj X :=
  ExactModelEquivalence.backward (evaluationModelEquivalence X)
    (evaluationSmallEquivalence_inverse_exact X)

/-- The original unit compares actual evaluation and its actual normalized inverse. -/
def evaluationInverseUnit (X : Scheme.{u}ᵒᵖ) :
    (evaluationModel X ≫ evaluationInverseModel X).functor ≅
      (𝟙 (globalModel.obj X) : globalModel.obj X ⟶ globalModel.obj X).functor :=
  ExactModelEquivalence.unitIso (evaluationModelEquivalence X) (evaluationModel X).exact
    (evaluationSmallEquivalence_inverse_exact X) (evaluationModel X).zero

/-- The original counit retains the same actual inverse zero normalization. -/
def evaluationInverseCounit (X : Scheme.{u}ᵒᵖ) :
    (evaluationInverseModel X ≫ evaluationModel X).functor ≅
      (𝟙 (modelOf (boundedFlatPerfectWaldhausen X.unop)) :
        modelOf (boundedFlatPerfectWaldhausen X.unop) ⟶
          modelOf (boundedFlatPerfectWaldhausen X.unop)).functor :=
  ExactModelEquivalence.counitIso (evaluationModelEquivalence X) (evaluationModel X).exact
    (evaluationSmallEquivalence_inverse_exact X) (evaluationModel X).zero

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
