/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassBottomScalarEdge
public import Quillen.Topology.Realization.SimplexGridBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassCommonChartSimplex

/-! Exact scalar edge paths to compare in the bottom/chart common-reference merge. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Convexity Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassLaurentBottomFace

/-- The full positive boundary path of the actual bottom parameter, with its original speed. -/
theorem parameter_left (r : unitInterval) :
    parameter.{u} (r, 0) = binaryPath (k := 14) 6 7 8 r := by
  change SimplexGrid.parameter.{u + 1} 4 2
    (BassProjectionPath.parameter 0, binaryPath (k := 2) 0 1 2 r) = _
  rw [Path.source, SimplexGrid.parameter_row]
  exact map_binaryPath (SimplexGrid.rowFace 4 2 2) 0 1 2 r

/-- The full negative boundary path of the same bottom parameter. -/
theorem parameter_right (r : unitInterval) :
    parameter.{u} (r, 1) = binaryPath (k := 14) 12 13 14 r := by
  change SimplexGrid.parameter.{u + 1} 4 2
    (BassProjectionPath.parameter 1, binaryPath (k := 2) 0 1 2 r) = _
  rw [Path.target, SimplexGrid.parameter_row]
  exact map_binaryPath (SimplexGrid.rowFace 4 2 4) 0 1 2 r

end Quillen.PerfectComplexes.BassLaurentBottomFace
namespace Quillen.PerfectComplexes.BassOverlap

/-- The fixed positive chart's whole bottom edge selects these exact common-chart nodes. -/
theorem plus_lower_parameter (r : unitInterval) :
    StdSimplex.map plusFace.toOrderHom
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 0)) =
        binaryPath (k := 35) 15 16 17 r := by
  rw [DoubleSquareScalarPaths.coefficientPausedSquareParameter_left]
  exact map_binaryPath plusFace 15 16 17 r

/-- The negative chart's whole bottom edge selects its own corresponding common-chart nodes. -/
theorem minus_lower_parameter (r : unitInterval) :
    StdSimplex.map minusFace.toOrderHom
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 0)) =
        binaryPath (k := 35) 33 34 35 r := by
  rw [DoubleSquareScalarPaths.coefficientPausedSquareParameter_left]
  exact map_binaryPath minusFace 15 16 17 r

end Quillen.PerfectComplexes.BassOverlap
