/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0Native
public import Quillen.Topology.Path.SimplexCollapsedEdges

/-! All four scalar edge paths of the exact original H0 cylinder face. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Convexity Quillen.SimplexParameters
open scoped Topology unitInterval
namespace Quillen.PerfectComplexes.BassH0Diagram
open ProjectionRectangleParameters

/-- Original positive projection comparison edge. -/
theorem parameter_left (s : unitInterval) : parameter (s, 0) = L plusFace s :=
  collapsed_left_path boundaryParameter s

/-- Original separate inverse projection comparison edge. -/
theorem parameter_right (s : unitInterval) : parameter (s, 1) = L minusFace s :=
  collapsed_right_path boundaryParameter s

/-- Original source Bass cylinder path after coefficient change. -/
theorem parameter_zero (t : unitInterval) :
    parameter (0, t) = ((D plusFace).symm.trans (D minusFace)) t :=
  collapsed_zero_path boundaryParameter t

/-- Original target cylinder path, including both polynomial-square tracks. -/
theorem parameter_one (t : unitInterval) :
    parameter (1, t) = ((Ppath plusFace).trans
      (((K plusFace).symm.trans (K minusFace)).trans (Ppath minusFace).symm)) t :=
  collapsed_top_path boundaryParameter t

end Quillen.PerfectComplexes.BassH0Diagram
