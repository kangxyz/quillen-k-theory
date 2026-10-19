/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedBoundary
public import Quillen.KTheory.Bass.SchemeModelRowNormalizedInitialBoundary

/-!
# The genuine returned tensor cup followed by the original boundary

The source operation is defined by inverse-prefix normalization of the actual returned
first-S tensor cell before the Laurent inclusion. The evaluation/unitor moving prism
and the unchanged source null compare it with the independently normalized internal
cell. This is a common-target comparison, not a definition by the current transition.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex GeometricSeedCospan ModelDiagramRowInterchange

/-- The independently normalized internal cell, before its actual boundary inclusion. -/
def normalizedInitialCupBoundary (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  RowRefinement.normalizedOperation
    (initial (ParameterModels.ambient Q) (laurent.op.obj X))
    (initial_point (ParameterModels.ambient Q) (laurent.op.obj X)) _ (initialCell Q X) ≫
      parameterLoopingMap (originalRowInclusion Q X)

/-- The genuine returned tensor first-S cell is normalized before the original boundary map. -/
def returnedNormalizedCupBoundary (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  RowRefinement.normalizedOperation
    (initial (ParameterModels.ambient Q) (laurent.op.obj X))
    (initial_point (ParameterModels.ambient Q) (laurent.op.obj X)) _
    (returnedTensorCell Q X) ≫ parameterLoopingMap (originalRowInclusion Q X)

/-- Actual normalization/inclusion naturality retains the internal operation as a whole map. -/
theorem normalizedInitialCupBoundary_eq (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    normalizedInitialCupBoundary Q X =
      RowRefinement.normalizedOperation
        (DiagramRowInterchange.cone squareFunctor (initialDiagram Q)
          (initial (ParameterModels.ambient Q)) (initial_point (ParameterModels.ambient Q))
          (initial_naturality (ParameterModels.ambient Q)) X)
        (DiagramRowInterchange.cone_point squareFunctor (initialDiagram Q)
          (initial (ParameterModels.ambient Q)) (initial_point (ParameterModels.ambient Q))
          (initial_naturality (ParameterModels.ambient Q)) X)
        (originalBoundaryEndpoint Q X)
        ((initialCell Q X).postcomp (originalRowInclusion Q X)) :=
  RowRefinement.normalizedOperation_postcomp
    (initial (ParameterModels.ambient Q) (laurent.op.obj X))
    (DiagramRowInterchange.cone squareFunctor (initialDiagram Q)
      (initial (ParameterModels.ambient Q)) (initial_point (ParameterModels.ambient Q))
      (initial_naturality (ParameterModels.ambient Q)) X)
    (initial_point (ParameterModels.ambient Q) (laurent.op.obj X))
    (DiagramRowInterchange.cone_point squareFunctor (initialDiagram Q)
      (initial (ParameterModels.ambient Q)) (initial_point (ParameterModels.ambient Q))
      (initial_naturality (ParameterModels.ambient Q)) X)
    (mappingConeInclusion (StrictSquare.comparison
      ((initialDiagram Q).mapArrow.mapArrow.obj (squareFunctor.obj X))))
    (fun _ _ => rfl) _ (initialCell Q X)

/-- Actual normalization/inclusion naturality retains the returned tensor operation as a whole map.
-/
theorem returnedNormalizedCupBoundary_eq (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    returnedNormalizedCupBoundary Q X =
      RowRefinement.normalizedOperation
        (DiagramRowInterchange.cone squareFunctor (initialDiagram Q)
          (initial (ParameterModels.ambient Q)) (initial_point (ParameterModels.ambient Q))
          (initial_naturality (ParameterModels.ambient Q)) X)
        (DiagramRowInterchange.cone_point squareFunctor (initialDiagram Q)
          (initial (ParameterModels.ambient Q)) (initial_point (ParameterModels.ambient Q))
          (initial_naturality (ParameterModels.ambient Q)) X)
        _ (returnedBoundaryCell Q X) :=
  RowRefinement.normalizedOperation_postcomp
    (initial (ParameterModels.ambient Q) (laurent.op.obj X))
    (DiagramRowInterchange.cone squareFunctor (initialDiagram Q)
      (initial (ParameterModels.ambient Q)) (initial_point (ParameterModels.ambient Q))
      (initial_naturality (ParameterModels.ambient Q)) X)
    (initial_point (ParameterModels.ambient Q) (laurent.op.obj X))
    (DiagramRowInterchange.cone_point squareFunctor (initialDiagram Q)
      (initial (ParameterModels.ambient Q)) (initial_point (ParameterModels.ambient Q))
      (initial_naturality (ParameterModels.ambient Q)) X)
    (mappingConeInclusion (StrictSquare.comparison
      ((initialDiagram Q).mapArrow.mapArrow.obj (squareFunctor.obj X))))
    (fun _ _ => rfl) _ (returnedTensorCell Q X)

/-- The genuine returned tensor cup/boundary and independent internal operation share a whole
comparison, preserving the original evaluation movement and source null. -/
def returnedNormalizedCupBoundaryHomotopy (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    Homotopy (returnedNormalizedCupBoundary Q X) (normalizedInitialCupBoundary Q X) :=
  (returnedBoundaryNormalization Q X).symm.cast
    (returnedNormalizedCupBoundary_eq Q X).symm (normalizedInitialCupBoundary_eq Q X).symm

/-- The initial independently realized operation is exactly the stage-zero normalized boundary.
-/
theorem normalizedInitialCupBoundary_stage_zero (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    normalizedInitialCupBoundary Q X =
      SchemeModelRowSeed.normalizedBoundary (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q)
        (ParameterLaurentUnit.ambientUnit_naturality Q) 0 X := by
  exact (SchemeModelRowSeed.normalizedBoundary_zero (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q)
    (ParameterLaurentUnit.ambientUnit_naturality Q) X).symm

/-- The genuine returned tensor cup followed by the boundary has the prescribed stage-zero
proper-row forward comparison, through the whole moving-endpoint normalization prism. -/
def returnedNormalizedForwardHomotopy (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    Homotopy (returnedNormalizedCupBoundary Q X)
      (SchemeModelRowSeed.forward (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q)
        (ParameterLaurentUnit.ambientUnit_naturality Q) 0 X) :=
  ((returnedNormalizedCupBoundaryHomotopy Q X).cast rfl
    (normalizedInitialCupBoundary_stage_zero Q X)).trans
      (SchemeModelRowSeed.normalizedBoundaryHomotopy (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q)
        (ParameterLaurentUnit.ambientUnit_naturality Q) 0 X)

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
