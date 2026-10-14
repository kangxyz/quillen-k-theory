/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1InternalNodeJoins

/-! Exact scalar words on every internal H1 seam, retaining all original speeds and reversals. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH1Join

/-- The full original positive first-cell boundary, at its literal lower-half cylinder time. -/
theorem first_plus_parameter (t : unitInterval) :
    StdSimplex.map (fun i ↦ BassH0Diagram.plusFace.toOrderHom (polynomialWordIndex i))
      (NativeSquareFiveSimplex.parameter t) = BassH0Diagram.parameter (1, lower t) := by
  rw [BassH0Diagram.parameter_one, path_lower]
  exact BassSupportOrder.map_two_binary
    (fun i ↦ BassH0Diagram.plusFace.toOrderHom (polynomialWordIndex i)) 0 1 2 3 4 t

/-- The inverse first-cell boundary retains its original last-quarter cylinder time and reversal. -/
theorem first_minus_parameter (t : unitInterval) :
    StdSimplex.map (fun i ↦ BassH0Diagram.minusFace.toOrderHom (polynomialWordIndex i))
      (NativeSquareFiveSimplex.parameter (unitInterval.symm t)) =
      BassH0Diagram.parameter (1, upper (upper t)) := by
  rw [BassH0Diagram.parameter_one, path_upper, path_upper]
  exact BassSupportOrder.map_two_binary
    (fun i ↦ BassH0Diagram.minusFace.toOrderHom (polynomialWordIndex i))
    0 1 2 3 4 (unitInterval.symm t)

/-- The complete original positive chart path of the middle component. -/
theorem middle_plus_parameter (s : unitInterval) :
    StdSimplex.map (fun i ↦ BassH0Diagram.plusFace.toOrderHom (chartWordIndex i))
      (NativeSquareFiveSimplex.parameter s) = BassH0Diagram.parameter (s, 0) := by
  rw [BassH0Diagram.parameter_left]
  exact BassSupportOrder.map_two_binary
    (fun i ↦ BassH0Diagram.plusFace.toOrderHom (chartWordIndex i)) 0 1 2 3 4 s

/-- The complete separate inverse chart path of the middle component. -/
theorem middle_minus_parameter (s : unitInterval) :
    StdSimplex.map (fun i ↦ BassH0Diagram.minusFace.toOrderHom (chartWordIndex i))
      (NativeSquareFiveSimplex.parameter s) = BassH0Diagram.parameter (s, 1) := by
  rw [BassH0Diagram.parameter_right]
  exact BassSupportOrder.map_two_binary
    (fun i ↦ BassH0Diagram.minusFace.toOrderHom (chartWordIndex i)) 0 1 2 3 4 s

/-- The actual positive product restricts to the literal source column of its second square. -/
theorem product_plus_column_parameter (t : unitInterval) :
    BassH1Components.plusParameter.{u} (0, t) =
      StdSimplex.map (Quillen.SimplexGrid.columnFace 4 4 2).toOrderHom
        (NativeSquareFiveSimplex.parameter t) := by
  change Quillen.SimplexGrid.parameter.{u + 1} 4 4
    (NativeSquareFiveSimplex.parameter t, NativeSquareFiveSimplex.parameter 0) = _
  rw [Path.source]
  exact Quillen.SimplexGrid.parameter_column 4 4 2 _

/-- The inverse product restricts to the same genuine column with its native time reversal. -/
theorem product_minus_column_parameter (t : unitInterval) :
    BassH1Components.minusParameter.{u} (0, t) =
      StdSimplex.map (Quillen.SimplexGrid.columnFace 4 4 2).toOrderHom
        (NativeSquareFiveSimplex.parameter (unitInterval.symm t)) := by
  change Quillen.SimplexGrid.parameter.{u + 1} 4 4
    (NativeSquareFiveSimplex.parameter (unitInterval.symm t),
      NativeSquareFiveSimplex.parameter 0) = _
  rw [Path.source]
  exact Quillen.SimplexGrid.parameter_column 4 4 2 _

/-- The whole positive product target row uses the actual realization product homeomorphism. -/
theorem product_plus_row_parameter (s : unitInterval) :
    BassH1Components.plusParameter.{u} (s, 1) =
      StdSimplex.map (Quillen.SimplexGrid.rowFace 4 4 4).toOrderHom
        (NativeSquareFiveSimplex.parameter s) := by
  change Quillen.SimplexGrid.parameter.{u + 1} 4 4
    (NativeSquareFiveSimplex.parameter 1, NativeSquareFiveSimplex.parameter s) = _
  rw [Path.target]
  exact Quillen.SimplexGrid.parameter_row 4 4 4 _

/-- The inverse product's opposite end retains its original reversal and the same target row. -/
theorem product_minus_row_parameter (s : unitInterval) :
    BassH1Components.minusParameter.{u} (s, 0) =
      StdSimplex.map (Quillen.SimplexGrid.rowFace 4 4 4).toOrderHom
        (NativeSquareFiveSimplex.parameter s) := by
  change Quillen.SimplexGrid.parameter.{u + 1} 4 4
    (NativeSquareFiveSimplex.parameter (unitInterval.symm 0),
      NativeSquareFiveSimplex.parameter s) = _
  rw [unitInterval.symm_zero, Path.target]
  exact Quillen.SimplexGrid.parameter_row 4 4 4 _

end Quillen.PerfectComplexes.BassH1Join
