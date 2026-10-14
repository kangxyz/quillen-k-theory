/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MSourceBoundaryNodes

/-! Complete original source-boundary scalar words on both actual reference families. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity Quillen.SimplexParameters Quillen.NativePathCells
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMOuterJoin

/-- The original polynomial moving source is its literal two-normalization native square word. -/
theorem moving_source_word (t : unitInterval) :
    StdSimplex.map movingSourceWordIndex (NativeSquareFiveSimplex.parameter t) =
      DoubleSquareScalarPaths.coefficientMovingSquareParameter (0, t) :=
  (BassSupportOrder.map_two_binary movingSourceWordIndex 0 1 2 3 4 t).trans
    (collapsed_zero_path DoubleSquareScalarPaths.coefficientBoundaryParameter t).symm

/-- The complete first positive source cell has its unchanged original dyadic time. -/
theorem source_plus_parameter (t : unitInterval) :
    StdSimplex.map sourcePlusIndex (NativeSquareFiveSimplex.parameter t) =
      BassMVertexOrder.parameter.{u} (0, lower t) := by
  rw [BassMVertexOrder.parameter_plus]
  change _ = StdSimplex.map BassMVertexOrder.plusIndex
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (0, t))
  rw [← moving_source_word, ← StdSimplex.map_comp]
  rfl

/-- The original middle source is the actual realization-product source row. -/
theorem source_middle_parameter (t : unitInterval) :
    StdSimplex.map sourceMiddleIndex (NativeSquareFiveSimplex.parameter t) =
      BassMVertexOrder.parameter.{u} (0, upper (lower t)) := by
  rw [BassMVertexOrder.parameter_middle]
  change _ = StdSimplex.map BassMVertexOrder.middleIndex
    (Quillen.SimplexGrid.parameter.{u + 1} 2 4
      (binaryPath (k := 2) 0 1 2 0, BassProjectionPath.parameter t))
  rw [Path.source, Quillen.SimplexGrid.parameter_row, ← StdSimplex.map_comp]
  rfl

/-- The inverse source cell retains its original final-quarter coordinate and path reversal. -/
theorem source_minus_parameter (t : unitInterval) :
    StdSimplex.map sourceMinusIndex (NativeSquareFiveSimplex.parameter (unitInterval.symm t)) =
      BassMVertexOrder.parameter.{u} (0, upper (upper t)) := by
  rw [BassMVertexOrder.parameter_minus]
  change _ = StdSimplex.map BassMVertexOrder.minusIndex
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (0, unitInterval.symm t))
  rw [← moving_source_word, ← StdSimplex.map_comp]
  rfl

/-- The same entire original word labels the fixed H0 positive target cell. -/
theorem old_source_plus_parameter (t : unitInterval) :
    StdSimplex.map oldSourcePlusIndex (NativeSquareFiveSimplex.parameter t) =
      BassH1Order.h0Parameter (1, lower t) := by
  change _ = StdSimplex.map BassH1Order.oldIndex
    (StdSimplex.map BassSupportOrder.h0Index (BassH0Diagram.parameter (1, lower t)))
  rw [← BassH1Join.first_plus_parameter, ← StdSimplex.map_comp, ← StdSimplex.map_comp]
  rfl

/-- The fixed H0 middle target cell has the same complete unchanged projection path word. -/
theorem old_source_middle_parameter (t : unitInterval) :
    StdSimplex.map oldSourceMiddleIndex (NativeSquareFiveSimplex.parameter t) =
      BassH1Order.h0Parameter (1, upper (lower t)) := by
  change _ = StdSimplex.map BassH1Order.oldIndex
    (StdSimplex.map BassSupportOrder.h0Index
      (BassH0Diagram.parameter (1, upper (lower t))))
  rw [← BassH1Join.first_middle_parameter, ← StdSimplex.map_comp, ← StdSimplex.map_comp]
  rfl

/-- The fixed H0 inverse target cell retains its literal reversed path and final-quarter speed. -/
theorem old_source_minus_parameter (t : unitInterval) :
    StdSimplex.map oldSourceMinusIndex (NativeSquareFiveSimplex.parameter (unitInterval.symm t)) =
      BassH1Order.h0Parameter (1, upper (upper t)) := by
  change _ = StdSimplex.map BassH1Order.oldIndex
    (StdSimplex.map BassSupportOrder.h0Index
      (BassH0Diagram.parameter (1, upper (upper t))))
  rw [← BassH1Join.first_minus_parameter, ← StdSimplex.map_comp, ← StdSimplex.map_comp]
  rfl

end Quillen.PerfectComplexes.BassMOuterJoin
