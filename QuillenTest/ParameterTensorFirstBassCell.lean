/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorFirstBassCell
import Quillen.KTheory.Bass.ModelUnitRowCellBassNaturality

/-! # Independent first Bass-stage coordinate regression

The actual ambient parameter cell preserves the old loop separately from both row coordinates.
These tests specialize the genuine cone descent, rather than replacing its input by one cell.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace QuillenTest.ParameterTensorFirstBassCell
open GeometricSeedCospan GeometricSquareInterchange

private abbrev originalCone (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  (ConeTrack.diagram squareFunctor (ParameterModels.ambient Q ⋙ prespectrumFunctor)).obj X

/-- An arbitrary old input loop retains its original time, independently of unit and row. -/
theorem positive_coordinates (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (k : ℕ)
    (r s t : unitInterval)
    (γ : Path ((originalCone Q X).point (k + 1)) ((originalCone Q X).point (k + 1))) :
    Path.toContinuousMap (Path.toContinuousMap
      ((firstBassCell Q X).level (k + 1) (r, γ)) s) t =
    Path.toContinuousMap
      ((ModelUnitRowCellCone.coneCell laurent.op coefficient (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
        squareFunctor (interchange (laurentProjection (.of (ULift.{u} ℤ)))) X).level
          (k + 1) (r, γ t)) s :=
  ModelUnitRowCellCone.bassCell_succ laurent.op coefficient (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
    squareFunctor (interchange (laurentProjection (.of (ULift.{u} ℤ)))) X k r s t γ

/-- Degree zero preserves both row times and the arbitrary original input-loop time. -/
theorem zero_coordinates (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    (v r s t : unitInterval)
    (γ : Path ((originalCone Q X).point 0) ((originalCone Q X).point 0)) :
    Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap
      ((firstBassCell Q X).level 0 (v, γ)) r) s) t =
    Path.toContinuousMap (Path.toContinuousMap
      ((ModelUnitRowCellCone.coneCell laurent.op coefficient (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
        squareFunctor (interchange (laurentProjection (.of (ULift.{u} ℤ)))) X).level
          0 (v, γ t)) r) s :=
  ModelUnitRowCellCone.bassCell_zero laurent.op coefficient (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
    squareFunctor (interchange (laurentProjection (.of (ULift.{u} ℤ)))) X v r s t γ

/-- Every actual scheme arrow preserves the whole independent first-stage cell at the same time. -/
theorem scheme_naturality (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ}
    (g : X ⟶ Y) (t : unitInterval) :
    ((strictDiagramFunctor squareFunctor).obj
        (ParameterModels.ambient Q ⋙ prespectrumFunctor)).map g ≫
        (firstBassCell Q Y).at t =
      (firstBassCell Q X).at t ≫
        (ModelUnitRowCellCone.bassRefined (ParameterModels.ambient Q) squareFunctor).map
          (laurent.op.map g) :=
  (ModelUnitRowCellCone.bassCellTimeSlice laurent.op coefficient (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
    squareFunctor (interchange (laurentProjection (.of (ULift.{u} ℤ))))
    (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ)))) t).naturality g

end QuillenTest.ParameterTensorFirstBassCell
