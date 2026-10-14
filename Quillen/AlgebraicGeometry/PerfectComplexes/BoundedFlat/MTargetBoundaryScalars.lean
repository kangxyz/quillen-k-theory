/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MSourceBoundaryScalars
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MAllBoundaryNodes

/-! Literal five-piece scalar boundary words of both original M stages. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity Quillen.SimplexParameters Quillen.NativePathCells
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMOuterJoin

abbrev firstTargetPath := (binaryPath (k := 17) 5 7 17).symm.trans (binaryPath 5 6 13)
abbrev secondTargetPath := (binaryPath (k := 17) 9 12 13).symm.trans (binaryPath 9 10 11)

/-- The original target boundary is exactly the native composite-square word at unchanged speed. -/
theorem moving_target_word (t : unitInterval) :
    DoubleSquareScalarPaths.coefficientMovingSquareParameter (1, t) =
      (firstTargetPath.trans secondTargetPath) t := by
  change collapsed DoubleSquareScalarPaths.coefficientBoundaryParameter (1, t) = _
  rw [collapsed_top_path]
  simp only [DoubleSquareScalarPaths.originalComparisonSource, Path.trans_symm, Path.symm_symm]

/-- The first original target path retains its complete five-node scalar word. -/
theorem first_target_word (t : unitInterval) :
    StdSimplex.map firstTargetWordIndex (NativeSquareFiveSimplex.parameter t) = firstTargetPath t :=
  BassSupportOrder.map_two_binary firstTargetWordIndex 0 1 2 3 4 t

/-- The second original target path retains its separate five-node scalar word. -/
theorem second_target_word (t : unitInterval) :
    StdSimplex.map secondTargetWordIndex (NativeSquareFiveSimplex.parameter t) =
      secondTargetPath t :=
  BassSupportOrder.map_two_binary secondTargetWordIndex 0 1 2 3 4 t

/-- The first path uses the original first quarter of the full first-stage target boundary. -/
theorem target_first_plus_parameter (t : unitInterval) :
    StdSimplex.map targetFirstPlusIndex (NativeSquareFiveSimplex.parameter t) =
      BassMVertexOrder.parameter.{u} (1, lower (lower t)) := by
  rw [BassMVertexOrder.parameter_plus]
  change _ = StdSimplex.map BassMVertexOrder.plusIndex
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (1, lower t))
  rw [moving_target_word, path_lower, ← first_target_word, ← StdSimplex.map_comp]
  rfl

/-- The second path retains the original second quarter of the positive target half. -/
theorem target_second_plus_parameter (t : unitInterval) :
    StdSimplex.map targetSecondPlusIndex (NativeSquareFiveSimplex.parameter t) =
      BassMVertexOrder.parameter.{u} (1, lower (upper t)) := by
  rw [BassMVertexOrder.parameter_plus]
  change _ = StdSimplex.map BassMVertexOrder.plusIndex
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (1, upper t))
  rw [moving_target_word, path_upper, ← second_target_word, ← StdSimplex.map_comp]
  rfl

/-- The central path retains the actual product target row and cylinder middle quarter. -/
theorem target_middle_parameter (t : unitInterval) :
    StdSimplex.map targetMiddleIndex (NativeSquareFiveSimplex.parameter t) =
      BassMVertexOrder.parameter.{u} (1, upper (lower t)) := by
  rw [BassMVertexOrder.parameter_middle]
  change _ = StdSimplex.map BassMVertexOrder.middleIndex
    (Quillen.SimplexGrid.parameter.{u + 1} 2 4
      (binaryPath (k := 2) 0 1 2 1, BassProjectionPath.parameter t))
  rw [Path.target, Quillen.SimplexGrid.parameter_row, ← StdSimplex.map_comp]
  rfl

/-- The fourth path is the actual inverse second square, with its original reversed time. -/
theorem target_second_minus_parameter (t : unitInterval) :
    StdSimplex.map targetSecondMinusIndex
      (NativeSquareFiveSimplex.parameter (unitInterval.symm t)) =
      BassMVertexOrder.parameter.{u} (1, upper (upper (lower t))) := by
  rw [BassMVertexOrder.parameter_minus]
  change _ = StdSimplex.map BassMVertexOrder.minusIndex
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (1, unitInterval.symm (lower t)))
  rw [moving_target_word]
  change _ = StdSimplex.map BassMVertexOrder.minusIndex
    ((firstTargetPath.trans secondTargetPath).symm (lower t))
  rw [Path.trans_symm, path_lower]
  change _ = StdSimplex.map BassMVertexOrder.minusIndex (secondTargetPath (unitInterval.symm t))
  rw [← second_target_word, ← StdSimplex.map_comp]
  rfl

/-- The final path retains the actual inverse first square and the original final eighth. -/
theorem target_first_minus_parameter (t : unitInterval) :
    StdSimplex.map targetFirstMinusIndex
      (NativeSquareFiveSimplex.parameter (unitInterval.symm t)) =
      BassMVertexOrder.parameter.{u} (1, upper (upper (upper t))) := by
  rw [BassMVertexOrder.parameter_minus]
  change _ = StdSimplex.map BassMVertexOrder.minusIndex
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (1, unitInterval.symm (upper t)))
  rw [moving_target_word]
  change _ = StdSimplex.map BassMVertexOrder.minusIndex
    ((firstTargetPath.trans secondTargetPath).symm (upper t))
  rw [Path.trans_symm, path_upper]
  change _ = StdSimplex.map BassMVertexOrder.minusIndex (firstTargetPath (unitInterval.symm t))
  rw [← first_target_word, ← StdSimplex.map_comp]
  rfl

/-- The fixed H1 labels retain the complete first native reassociation path. -/
theorem old_first_plus_word (t : unitInterval) :
    StdSimplex.map oldTargetFirstPlusIndex (NativeSquareFiveSimplex.parameter t) =
      BassMReassociation.Ppath t :=
  BassSupportOrder.map_two_binary oldTargetFirstPlusIndex 0 1 2 3 4 t

/-- The fixed H1 labels retain the complete second native reassociation path. -/
theorem old_second_plus_word (t : unitInterval) :
    StdSimplex.map oldTargetSecondPlusIndex (NativeSquareFiveSimplex.parameter t) =
      BassMReassociation.Qpath t :=
  BassSupportOrder.map_two_binary oldTargetSecondPlusIndex 0 1 2 3 4 t

/-- The fixed H1 central path retains both actual projection normalization pieces. -/
theorem old_middle_word (t : unitInterval) :
    StdSimplex.map oldTargetMiddleIndex (NativeSquareFiveSimplex.parameter t) =
      BassMReassociation.Tpath t :=
  BassSupportOrder.map_two_binary oldTargetMiddleIndex 0 1 2 3 4 t

/-- The fourth original path retains the actual inverse second-square reversal. -/
theorem old_second_minus_word (t : unitInterval) :
    StdSimplex.map oldTargetSecondMinusIndex
      (NativeSquareFiveSimplex.parameter (unitInterval.symm t)) =
      BassMReassociation.Upath t :=
  BassSupportOrder.map_two_binary oldTargetSecondMinusIndex 0 1 2 3 4 (unitInterval.symm t)

/-- The final original path retains its distinct inverse first-square reversal. -/
theorem old_first_minus_word (t : unitInterval) :
    StdSimplex.map oldTargetFirstMinusIndex
      (NativeSquareFiveSimplex.parameter (unitInterval.symm t)) =
      BassMReassociation.Vpath t :=
  BassSupportOrder.map_two_binary oldTargetFirstMinusIndex 0 1 2 3 4 (unitInterval.symm t)

end Quillen.PerfectComplexes.BassMOuterJoin
