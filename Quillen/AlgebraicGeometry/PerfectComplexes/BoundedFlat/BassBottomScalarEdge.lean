/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassLaurentBottomFace
public import Quillen.Topology.Path.SimplexCollapsedBoundary

/-! The actual scalar lower edge of the fixed paused chart surface. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Convexity
open scoped Topology unitInterval
namespace Quillen.PerfectComplexes.DoubleSquareScalarPaths

/-- Both fixed chart scalar surfaces have precisely this whole original Laurent-composition edge. -/
theorem coefficientPausedSquareParameter_left (r : unitInterval) :
    coefficientPausedSquareParameter (r, 0) = targetChart r :=
  Quillen.SimplexParameters.collapsed_left_path _ r

end Quillen.PerfectComplexes.DoubleSquareScalarPaths
