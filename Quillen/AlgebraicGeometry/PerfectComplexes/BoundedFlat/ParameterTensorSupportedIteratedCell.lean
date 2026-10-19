/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorSupportedInitialCell
public import Quillen.KTheory.Bass.ModelUnitRowCellIteration

/-! # Independent supported tensor-qualified cells at every original Bass stage

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
namespace Quillen.PerfectComplexes.ParameterTensorSupportedRow
open GlobalSectionChangeIndex GeometricSeedCospan GeometricSquareInterchange
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The independently constructed supported action cell at the original Bass stage. -/
def iteratedCell (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  ModelDiagramRowInterchange.iteratedCell laurent.op coefficient (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedUnit f) (ParameterLaurentTrack.supportedUnit_naturality f)
    squareFunctor (interchange (laurentProjection (.of (ULift.{u} ℤ))))
    (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ)))) i X

/-- The unchanged original supported action, with its actual finite diagram fixed explicitly. -/
def originalStageTrack (i : ℕ) :
    NaturalTrack.Track laurent.op coefficient
      ((strictDiagramIterate squareFunctor i).obj
        (ParameterModels.supported f ⋙ prespectrumFunctor)) :=
  NaturalTrack.Track.stages (L := laurent.op) (c := coefficient)
    (F := ParameterModels.supported f ⋙ prespectrumFunctor) squareFunctor
    (interchange (laurentProjection (.of (ULift.{u} ℤ))))
    (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ))))
    (ParameterLaurentTrack.supportedTrack f) i

/-- The genuine whole-cell comparison holds at every Bass stage and the same original time. -/
theorem iteratedCell_at_eq (i : ℕ) (X : Scheme.{u}ᵒᵖ)
    (t : unitInterval) :
    (iteratedCell f i X).at t = ((originalStageTrack f i).homotopy X).at t ≫
      (DiagramRowRefinement.comparison
        ((strictDiagramIterate squareFunctor i).obj
          (ParameterModels.supported f ⋙ prespectrumFunctor))
        (ModelDiagramRowInterchange.stage squareFunctor (ParameterModels.supported f) i)
        (ModelDiagramRowInterchange.stage_point squareFunctor (ParameterModels.supported f) i)
        (ModelDiagramRowInterchange.stage_naturality squareFunctor (ParameterModels.supported f) i)
        (ModelDiagramRowInterchange.stage_structure
          squareFunctor (ParameterModels.supported f) i)).app
          (laurent.op.obj X) :=
  ModelDiagramRowInterchange.iteratedCell_at_eq laurent.op coefficient (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedUnit f) (ParameterLaurentTrack.supportedUnit_naturality f)
    squareFunctor (interchange (laurentProjection (.of (ULift.{u} ℤ))))
    (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ)))) i X t

/-- At stage zero the construction retains the original independently realized initial cell. -/
theorem iteratedCell_zero_level (X : Scheme.{u}ᵒᵖ) (n : ℕ) :
    (iteratedCell f 0 X).level n = (initialCell f X).level n := rfl

end Quillen.PerfectComplexes.ParameterTensorSupportedRow
