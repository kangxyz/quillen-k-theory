/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1BottomJoinFace

/-! Exact whole scalar outer chart words, retaining the original pause, speeds and reversals. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH1Join

def outerFirstWordIndex : Fin 5 → Fin 18 := ![5, 7, 17, 6, 13]
def outerProductWordIndex : Fin 5 → Fin 18 := ![9, 12, 13, 10, 11]

/-- The original terminal pause leaves the whole target chart path literally unchanged. -/
theorem old_chart_one_parameter (s : unitInterval) :
    DoubleSquareScalarPaths.coefficientPausedSquareParameter (1, s) =
      DoubleSquareScalarPaths.originalComparisonSource s :=
  collapsed_top_path (pauseRightParameter DoubleSquareScalarPaths.coefficientBoundaryParameter) s

/-- The first half of the original chart endpoint has exactly this reversed two-binary word. -/
theorem old_chart_first_parameter (s : unitInterval) :
    StdSimplex.map outerFirstWordIndex (NativeSquareFiveSimplex.parameter s) =
      DoubleSquareScalarPaths.coefficientPausedSquareParameter (1, lower s) := by
  rw [old_chart_one_parameter]
  unfold DoubleSquareScalarPaths.originalComparisonSource
  rw [Path.trans_symm, path_lower, Path.trans_symm, Path.symm_symm]
  exact BassSupportOrder.map_two_binary outerFirstWordIndex 0 1 2 3 4 s

/-- The other half retains the literal original second square and the original half speed. -/
theorem old_chart_second_parameter (s : unitInterval) :
    StdSimplex.map outerProductWordIndex (NativeSquareFiveSimplex.parameter s) =
      DoubleSquareScalarPaths.coefficientPausedSquareParameter (1, upper s) := by
  rw [old_chart_one_parameter]
  unfold DoubleSquareScalarPaths.originalComparisonSource
  rw [Path.trans_symm, path_upper, Path.trans_symm, Path.symm_symm]
  exact BassSupportOrder.map_two_binary outerProductWordIndex 0 1 2 3 4 s

/-- The entire positive product outer edge is the actual realization-product row2 path. -/
theorem product_plus_outer_parameter (s : unitInterval) :
    BassH1Components.plusParameter.{u} (s, 0) =
      StdSimplex.map (Quillen.SimplexGrid.rowFace 4 4 2).toOrderHom
        (NativeSquareFiveSimplex.parameter s) := by
  change Quillen.SimplexGrid.parameter.{u + 1} 4 4
    (NativeSquareFiveSimplex.parameter 0, NativeSquareFiveSimplex.parameter s) = _
  rw [Path.source]
  exact Quillen.SimplexGrid.parameter_row 4 4 2 _

/-- The inverse product's opposite outer edge retains its original reversed cylinder time. -/
theorem product_minus_outer_parameter (s : unitInterval) :
    BassH1Components.minusParameter.{u} (s, 1) =
      StdSimplex.map (Quillen.SimplexGrid.rowFace 4 4 2).toOrderHom
        (NativeSquareFiveSimplex.parameter s) := by
  change Quillen.SimplexGrid.parameter.{u + 1} 4 4
    (NativeSquareFiveSimplex.parameter (unitInterval.symm 1),
      NativeSquareFiveSimplex.parameter s) = _
  rw [unitInterval.symm_one, Path.source]
  exact Quillen.SimplexGrid.parameter_row 4 4 2 _

/-- The fixed old62 positive chart's complete first half has these exact scalar node labels. -/
theorem old62_plus_first_parameter (s : unitInterval) :
    StdSimplex.map (fun i ↦ BassSupportOrder.oldIndex (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.plusFace.toOrderHom (outerFirstWordIndex i))))
      (NativeSquareFiveSimplex.parameter s) = BassSupportOrder.plusParameter (1, lower s) := by
  change _ = StdSimplex.map BassSupportOrder.oldIndex
    (StdSimplex.map BassReferenceMerge.chartFace.toOrderHom
      (StdSimplex.map BassOverlap.plusFace.toOrderHom
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (1, lower s))))
  rw [← old_chart_first_parameter, ← StdSimplex.map_comp, ← StdSimplex.map_comp,
    ← StdSimplex.map_comp]
  rfl

/-- The fixed old62 positive chart's entire second half retains its original scalar word. -/
theorem old62_plus_second_parameter (s : unitInterval) :
    StdSimplex.map (fun i ↦ BassSupportOrder.oldIndex (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.plusFace.toOrderHom (outerProductWordIndex i))))
      (NativeSquareFiveSimplex.parameter s) = BassSupportOrder.plusParameter (1, upper s) := by
  change _ = StdSimplex.map BassSupportOrder.oldIndex
    (StdSimplex.map BassReferenceMerge.chartFace.toOrderHom
      (StdSimplex.map BassOverlap.plusFace.toOrderHom
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (1, upper s))))
  rw [← old_chart_second_parameter, ← StdSimplex.map_comp, ← StdSimplex.map_comp,
    ← StdSimplex.map_comp]
  rfl

/-- The complete first half of the separate inverse old62 chart, with its actual node labels. -/
theorem old62_minus_first_parameter (s : unitInterval) :
    StdSimplex.map (fun i ↦ BassSupportOrder.oldIndex (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.minusFace.toOrderHom (outerFirstWordIndex i))))
      (NativeSquareFiveSimplex.parameter s) = BassSupportOrder.minusParameter (1, lower s) := by
  change _ = StdSimplex.map BassSupportOrder.oldIndex
    (StdSimplex.map BassReferenceMerge.chartFace.toOrderHom
      (StdSimplex.map BassOverlap.minusFace.toOrderHom
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (1, lower s))))
  rw [← old_chart_first_parameter, ← StdSimplex.map_comp, ← StdSimplex.map_comp,
    ← StdSimplex.map_comp]
  rfl

/-- The complete other half of the inverse old62 chart, without any reparameterized replacement. -/
theorem old62_minus_second_parameter (s : unitInterval) :
    StdSimplex.map (fun i ↦ BassSupportOrder.oldIndex (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.minusFace.toOrderHom (outerProductWordIndex i))))
      (NativeSquareFiveSimplex.parameter s) = BassSupportOrder.minusParameter (1, upper s) := by
  change _ = StdSimplex.map BassSupportOrder.oldIndex
    (StdSimplex.map BassReferenceMerge.chartFace.toOrderHom
      (StdSimplex.map BassOverlap.minusFace.toOrderHom
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (1, upper s))))
  rw [← old_chart_second_parameter, ← StdSimplex.map_comp, ← StdSimplex.map_comp,
    ← StdSimplex.map_comp]
  rfl

end Quillen.PerfectComplexes.BassH1Join
