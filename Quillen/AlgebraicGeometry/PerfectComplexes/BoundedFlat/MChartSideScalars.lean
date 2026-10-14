/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MTargetBoundaryScalars

/-! Original whole M/chart side words, including the literal terminal half pause. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity Quillen.SimplexParameters Quillen.NativePathCells
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMOuterJoin

/-- The actual moving square left side retains its complete target-composition binary path. -/
theorem moving_left_parameter (r : unitInterval) :
    DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, 0) =
      DoubleSquareScalarPaths.targetChart r :=
  collapsed_left_path DoubleSquareScalarPaths.coefficientBoundaryParameter r

/-- The old chart's whole right side is exactly the original binary path followed by its pause. -/
theorem paused_side_parameter (r : unitInterval) :
    DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 1) =
      (DoubleSquareScalarPaths.sourceChart.trans (Path.refl (StdSimplex.single 11))) r :=
  collapsed_right_path (pauseRightParameter DoubleSquareScalarPaths.coefficientBoundaryParameter) r

/-- The first half of the old chart side retains the native binary composition speed. -/
theorem paused_side_lower (r : unitInterval) :
    DoubleSquareScalarPaths.coefficientPausedSquareParameter (lower r, 1) =
      DoubleSquareScalarPaths.sourceChart r := by
  rw [paused_side_parameter, path_lower]

/-- The second half is the prescribed original fixed endpoint, for every parameter value. -/
theorem paused_side_upper (r : unitInterval) :
    DoubleSquareScalarPaths.coefficientPausedSquareParameter (upper r, 1) =
      StdSimplex.single 11 := by
  rw [paused_side_parameter, path_upper]
  rfl

/-- The complete positive first-stage side retains its exact original three-node word. -/
theorem vertex_plus_side_parameter (r : unitInterval) :
    StdSimplex.map sidePlusIndex (binaryPath (k := 2) 0 1 2 r) =
      BassMVertexOrder.parameter.{u} (r, 0) := by
  rw [BassMVertexOrder.parameter_zero]
  change _ = StdSimplex.map BassMVertexOrder.plusIndex
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, 0))
  rw [moving_left_parameter]
  exact (BassSupportOrder.map_any_binary sidePlusIndex 0 1 2 r).trans
    (BassSupportOrder.map_any_binary BassMVertexOrder.plusIndex 15 16 17 r).symm

/-- The inverse first-stage side retains its own complete word after the original reversal. -/
theorem vertex_minus_side_parameter (r : unitInterval) :
    StdSimplex.map sideMinusIndex (binaryPath (k := 2) 0 1 2 r) =
      BassMVertexOrder.parameter.{u} (r, 1) := by
  rw [BassMVertexOrder.parameter_one]
  change _ = StdSimplex.map BassMVertexOrder.minusIndex
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, unitInterval.symm 1))
  rw [unitInterval.symm_one, moving_left_parameter]
  exact (BassSupportOrder.map_any_binary sideMinusIndex 0 1 2 r).trans
    (BassSupportOrder.map_any_binary BassMVertexOrder.minusIndex 15 16 17 r).symm

/-- The old positive side's whole first half retains these exact common-family labels. -/
theorem old_plus_side_lower (r : unitInterval) :
    StdSimplex.map oldSidePlusIndex (binaryPath (k := 2) 0 1 2 r) =
      BassH1Order.plusParameter (lower r, 1) := by
  change _ = StdSimplex.map BassH1Order.oldIndex
    (StdSimplex.map BassSupportOrder.oldIndex
      (StdSimplex.map BassReferenceMerge.chartFace.toOrderHom
      (StdSimplex.map BassOverlap.plusFace.toOrderHom
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (lower r, 1)))))
  rw [paused_side_lower, ← StdSimplex.map_comp, ← StdSimplex.map_comp, ← StdSimplex.map_comp]
  exact (BassSupportOrder.map_any_binary oldSidePlusIndex 0 1 2 r).trans
    (BassSupportOrder.map_any_binary
      (fun i : Fin 18 ↦ BassH1Order.oldIndex (BassSupportOrder.oldIndex
        (BassReferenceMerge.chartFace.toOrderHom (BassOverlap.plusFace.toOrderHom i))))
      2 3 11 r).symm

/-- The inverse old side's whole first half retains its distinct original common-family labels. -/
theorem old_minus_side_lower (r : unitInterval) :
    StdSimplex.map oldSideMinusIndex (binaryPath (k := 2) 0 1 2 r) =
      BassH1Order.minusParameter (lower r, 1) := by
  change _ = StdSimplex.map BassH1Order.oldIndex
    (StdSimplex.map BassSupportOrder.oldIndex
      (StdSimplex.map BassReferenceMerge.chartFace.toOrderHom
      (StdSimplex.map BassOverlap.minusFace.toOrderHom
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (lower r, 1)))))
  rw [paused_side_lower, ← StdSimplex.map_comp, ← StdSimplex.map_comp, ← StdSimplex.map_comp]
  exact (BassSupportOrder.map_any_binary oldSideMinusIndex 0 1 2 r).trans
    (BassSupportOrder.map_any_binary
      (fun i : Fin 18 ↦ BassH1Order.oldIndex (BassSupportOrder.oldIndex
        (BassReferenceMerge.chartFace.toOrderHom (BassOverlap.minusFace.toOrderHom i))))
      2 3 11 r).symm

/-- The fixed positive chart pause retains the original terminal scalar endpoint. -/
theorem old_plus_side_upper (r : unitInterval) :
    BassH1Order.plusParameter (upper r, 1) = StdSimplex.single (oldSidePlusIndex 2) := by
  change StdSimplex.map BassH1Order.oldIndex
    (StdSimplex.map BassSupportOrder.oldIndex
      (StdSimplex.map BassReferenceMerge.chartFace.toOrderHom
      (StdSimplex.map BassOverlap.plusFace.toOrderHom
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (upper r, 1))))) = _
  rw [paused_side_upper]
  simp only [StdSimplex.map_single]
  rfl

/-- The inverse chart pause retains its separate original terminal scalar endpoint. -/
theorem old_minus_side_upper (r : unitInterval) :
    BassH1Order.minusParameter (upper r, 1) = StdSimplex.single (oldSideMinusIndex 2) := by
  change StdSimplex.map BassH1Order.oldIndex
    (StdSimplex.map BassSupportOrder.oldIndex
      (StdSimplex.map BassReferenceMerge.chartFace.toOrderHom
      (StdSimplex.map BassOverlap.minusFace.toOrderHom
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (upper r, 1))))) = _
  rw [paused_side_upper]
  simp only [StdSimplex.map_single]
  rfl

/-- The literal reassociation fixes the exact positive side endpoint at every original time. -/
theorem second_plus_side (r : unitInterval) :
    BassMReassociation.secondParameter (r, 0) = StdSimplex.single (oldSidePlusIndex 2) :=
  BassMReassociation.reassociation.symm.source r

/-- The same original word fixes its distinct inverse endpoint at every original time. -/
theorem second_minus_side (r : unitInterval) :
    BassMReassociation.secondParameter (r, 1) = StdSimplex.single (oldSideMinusIndex 2) :=
  BassMReassociation.reassociation.symm.target r

end Quillen.PerfectComplexes.BassMOuterJoin
