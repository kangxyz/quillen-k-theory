/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorInitialCell
public import Quillen.KTheory.Bass.ModelUnitRowCellIteration

/-! # Independent ambient tensor-qualified cells at every original Bass stage

The initial actual tensor/evaluation prism qualifies the literal parameter Model cell.
The later cells are constructed by the original finite cone and loop operations, retaining
all original action times and the computed row target. No new tensor compatibility is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex GeometricSeedCospan GeometricSquareInterchange

/-- The independently constructed ambient action cell at the original Bass stage. -/
def iteratedCell (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  ModelDiagramRowInterchange.iteratedCell laurent.op coefficient (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
    squareFunctor (interchange (laurentProjection (.of (ULift.{u} ℤ))))
    (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ)))) i X

/-- The unchanged original ambient action, with its actual finite diagram fixed explicitly. -/
def originalStageTrack (Q : Scheme.{u}) (i : ℕ) :
    NaturalTrack.Track laurent.op coefficient
      ((strictDiagramIterate squareFunctor i).obj
        (ParameterModels.ambient Q ⋙ prespectrumFunctor)) :=
  NaturalTrack.Track.stages (L := laurent.op) (c := coefficient)
    (F := ParameterModels.ambient Q ⋙ prespectrumFunctor) squareFunctor
    (interchange (laurentProjection (.of (ULift.{u} ℤ))))
    (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ))))
    (ParameterLaurentTrack.ambientTrack Q) i

/-- The genuine whole-cell comparison holds at every Bass stage and the same original time. -/
theorem iteratedCell_at_eq (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ)
    (t : unitInterval) :
    (iteratedCell Q i X).at t = ((originalStageTrack Q i).homotopy X).at t ≫
      (DiagramRowRefinement.comparison
        ((strictDiagramIterate squareFunctor i).obj
          (ParameterModels.ambient Q ⋙ prespectrumFunctor))
        (ModelDiagramRowInterchange.stage squareFunctor (ParameterModels.ambient Q) i)
        (ModelDiagramRowInterchange.stage_point squareFunctor (ParameterModels.ambient Q) i)
        (ModelDiagramRowInterchange.stage_naturality squareFunctor (ParameterModels.ambient Q) i)
        (ModelDiagramRowInterchange.stage_structure
          squareFunctor (ParameterModels.ambient Q) i)).app
          (laurent.op.obj X) :=
  ModelDiagramRowInterchange.iteratedCell_at_eq laurent.op coefficient (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
    squareFunctor (interchange (laurentProjection (.of (ULift.{u} ℤ))))
    (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ)))) i X t

/-- At stage zero the construction retains the original independently realized initial cell. -/
theorem iteratedCell_zero_level (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (n : ℕ) :
    (iteratedCell Q 0 X).level n = (initialCell Q X).level n := rfl

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
