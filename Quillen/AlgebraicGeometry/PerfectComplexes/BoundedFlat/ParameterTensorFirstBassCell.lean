/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorInitialCell
public import Quillen.KTheory.Bass.ModelUnitRowCellBass

/-! # Independent first Bass-stage cells on the literal ambient parameter diagram

The actual initial tensor/evaluation prism supplies the initial cell. Its original four corner
cells descend through the geometric square, inverse Laurent index map, forward cone row strength
and explicit old-loop/row conversion. The whole comparison retains the original first Bass track.
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

/-- The actual first-stage cell, constructed before comparison with the original scalar action. -/
def firstBassCell (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  ModelUnitRowCellCone.bassCell laurent.op coefficient (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
    squareFunctor (interchange (laurentProjection (.of (ULift.{u} ℤ)))) X

/-- The original first Bass action with its literal parameter diagram fixed explicitly. -/
def firstBassTrack (Q : Scheme.{u}) :
    NaturalTrack.Track laurent.op coefficient
      ((strictDiagramFunctor squareFunctor).obj
        (ParameterModels.ambient Q ⋙ prespectrumFunctor)) :=
  NaturalTrack.Track.bass (L := laurent.op) (c := coefficient)
    (F := ParameterModels.ambient Q ⋙ prespectrumFunctor) squareFunctor
    (interchange (laurentProjection (.of (ULift.{u} ℤ))))
    (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ))))
    (ParameterLaurentTrack.ambientTrack Q)

/-- The whole independent first-stage cell recovers the original Bass track at the same time. -/
theorem firstBassCell_at_eq (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (t : unitInterval) :
    (firstBassCell Q X).at t =
      ((firstBassTrack Q).homotopy X).at t ≫
      ModelUnitRowCellCone.bassComparison (ParameterModels.ambient Q) squareFunctor
        (laurent.op.obj X) :=
  ModelUnitRowCellCone.bassCell_at_eq laurent.op coefficient (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
    squareFunctor (interchange (laurentProjection (.of (ULift.{u} ℤ))))
    (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ)))) X t

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
