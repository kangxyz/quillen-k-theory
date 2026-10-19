/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorSupportedReturnedBoundary
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
namespace Quillen.PerfectComplexes.ParameterTensorSupportedRow
open GlobalSectionChangeIndex GeometricSeedCospan ModelDiagramRowInterchange
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The independently normalized internal cell, before its actual boundary inclusion. -/
def normalizedInitialCupBoundary (X : Scheme.{u}ᵒᵖ) :=
  RowRefinement.normalizedOperation
    (initial (ParameterModels.supported f) (laurent.op.obj X))
    (initial_point (ParameterModels.supported f) (laurent.op.obj X)) _ (initialCell f X) ≫
      parameterLoopingMap (originalRowInclusion f X)

/-- The genuine returned tensor first-S cell is normalized before the original boundary map. -/
def returnedNormalizedCupBoundary (X : Scheme.{u}ᵒᵖ) :=
  RowRefinement.normalizedOperation
    (initial (ParameterModels.supported f) (laurent.op.obj X))
    (initial_point (ParameterModels.supported f) (laurent.op.obj X)) _
    (returnedTensorCell f X) ≫ parameterLoopingMap (originalRowInclusion f X)

/-- Actual normalization/inclusion naturality retains the internal operation as a whole map. -/
theorem normalizedInitialCupBoundary_eq (X : Scheme.{u}ᵒᵖ) :
    normalizedInitialCupBoundary f X =
      RowRefinement.normalizedOperation
        (DiagramRowInterchange.cone squareFunctor (initialDiagram f)
          (initial (ParameterModels.supported f)) (initial_point (ParameterModels.supported f))
          (initial_naturality (ParameterModels.supported f)) X)
        (DiagramRowInterchange.cone_point squareFunctor (initialDiagram f)
          (initial (ParameterModels.supported f)) (initial_point (ParameterModels.supported f))
          (initial_naturality (ParameterModels.supported f)) X)
        (originalBoundaryEndpoint f X)
        ((initialCell f X).postcomp (originalRowInclusion f X)) :=
  RowRefinement.normalizedOperation_postcomp
    (initial (ParameterModels.supported f) (laurent.op.obj X))
    (DiagramRowInterchange.cone squareFunctor (initialDiagram f)
      (initial (ParameterModels.supported f)) (initial_point (ParameterModels.supported f))
      (initial_naturality (ParameterModels.supported f)) X)
    (initial_point (ParameterModels.supported f) (laurent.op.obj X))
    (DiagramRowInterchange.cone_point squareFunctor (initialDiagram f)
      (initial (ParameterModels.supported f)) (initial_point (ParameterModels.supported f))
      (initial_naturality (ParameterModels.supported f)) X)
    (mappingConeInclusion (StrictSquare.comparison
      ((initialDiagram f).mapArrow.mapArrow.obj (squareFunctor.obj X))))
    (fun _ _ => rfl) _ (initialCell f X)

/-- Actual normalization/inclusion naturality retains the returned tensor operation as a whole map.
-/
theorem returnedNormalizedCupBoundary_eq (X : Scheme.{u}ᵒᵖ) :
    returnedNormalizedCupBoundary f X =
      RowRefinement.normalizedOperation
        (DiagramRowInterchange.cone squareFunctor (initialDiagram f)
          (initial (ParameterModels.supported f)) (initial_point (ParameterModels.supported f))
          (initial_naturality (ParameterModels.supported f)) X)
        (DiagramRowInterchange.cone_point squareFunctor (initialDiagram f)
          (initial (ParameterModels.supported f)) (initial_point (ParameterModels.supported f))
          (initial_naturality (ParameterModels.supported f)) X)
        _ (returnedBoundaryCell f X) :=
  RowRefinement.normalizedOperation_postcomp
    (initial (ParameterModels.supported f) (laurent.op.obj X))
    (DiagramRowInterchange.cone squareFunctor (initialDiagram f)
      (initial (ParameterModels.supported f)) (initial_point (ParameterModels.supported f))
      (initial_naturality (ParameterModels.supported f)) X)
    (initial_point (ParameterModels.supported f) (laurent.op.obj X))
    (DiagramRowInterchange.cone_point squareFunctor (initialDiagram f)
      (initial (ParameterModels.supported f)) (initial_point (ParameterModels.supported f))
      (initial_naturality (ParameterModels.supported f)) X)
    (mappingConeInclusion (StrictSquare.comparison
      ((initialDiagram f).mapArrow.mapArrow.obj (squareFunctor.obj X))))
    (fun _ _ => rfl) _ (returnedTensorCell f X)

/-- The genuine returned tensor cup/boundary and independent internal operation share a whole
comparison, preserving the original evaluation movement and source null. -/
def returnedNormalizedCupBoundaryHomotopy (X : Scheme.{u}ᵒᵖ) :
    Homotopy (returnedNormalizedCupBoundary f X) (normalizedInitialCupBoundary f X) :=
  (returnedBoundaryNormalization f X).symm.cast
    (returnedNormalizedCupBoundary_eq f X).symm (normalizedInitialCupBoundary_eq f X).symm

/-- The initial independently realized operation is exactly the stage-zero normalized boundary.
-/
theorem normalizedInitialCupBoundary_stage_zero (X : Scheme.{u}ᵒᵖ) :
    normalizedInitialCupBoundary f X =
      SchemeModelRowSeed.normalizedBoundary (ParameterModels.supported f)
        (ParameterLaurentTrack.supportedUnit f)
        (ParameterLaurentTrack.supportedUnit_naturality f) 0 X :=
  (SchemeModelRowSeed.normalizedBoundary_zero (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedUnit f)
    (ParameterLaurentTrack.supportedUnit_naturality f) X).symm

/-- The genuine returned tensor cup followed by the boundary has the prescribed stage-zero
proper-row forward comparison, through the whole moving-endpoint normalization prism. -/
def returnedNormalizedForwardHomotopy (X : Scheme.{u}ᵒᵖ) :
    Homotopy (returnedNormalizedCupBoundary f X)
      (SchemeModelRowSeed.forward (ParameterModels.supported f)
        (ParameterLaurentTrack.supportedUnit f)
        (ParameterLaurentTrack.supportedUnit_naturality f) 0 X) :=
  ((returnedNormalizedCupBoundaryHomotopy f X).cast rfl
    (normalizedInitialCupBoundary_stage_zero f X)).trans
      (SchemeModelRowSeed.normalizedBoundaryHomotopy (ParameterModels.supported f)
        (ParameterLaurentTrack.supportedUnit f)
        (ParameterLaurentTrack.supportedUnit_naturality f) 0 X)

end Quillen.PerfectComplexes.ParameterTensorSupportedRow
