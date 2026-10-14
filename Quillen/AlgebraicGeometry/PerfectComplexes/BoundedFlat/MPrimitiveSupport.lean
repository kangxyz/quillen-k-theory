/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MGridProductFaces

/-! Exact primitive-face coverage of every point of the original first M stage. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Quillen.SimplexParameters Quillen.ParameterSupport
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMPrimitiveSupport

/-- Every point of the original moving square lies on one of its three original triple faces. -/
theorem moving_support (z : unitInterval × unitInterval) :
    ∃ (i : Fin 3) (w : StdSimplex ℝ (Fin 8)),
      StdSimplex.map (BassPrimitiveSupport.rectangleFace i).toOrderHom w =
        DoubleSquareScalarPaths.coefficientMovingSquareParameter z :=
  collapsed_in BassPrimitiveSupport.coefficient_boundary_in z

def coefficientEdgeSupport : Set (StdSimplex ℝ (Fin 3)) :=
  {z | ∃ (i : Fin 2) (w : StdSimplex ℝ (Fin 2)),
    StdSimplex.map (coefficientEdgeFace i).toOrderHom w = z}

/-- Each original coefficient normalization edge retains its actual one-simplex support. -/
theorem coefficient_edge_in (i : Fin 2) :
    PathIn coefficientEdgeSupport (edge (coefficientEdgeStart i) (coefficientEdgeEnd i)) := by
  intro t
  refine ⟨i, edge 0 1 t, ?_⟩
  exact BassSupportOrder.map_any_edge (coefficientEdgeFace i).toOrderHom 0 1 t

/-- The complete actual binary coefficient path has precisely these two original edge supports. -/
theorem coefficient_path_in : PathIn coefficientEdgeSupport (binaryPath (k := 2) 0 1 2) :=
  path_trans (coefficient_edge_in 0) (coefficient_edge_in 1)

/-- Both middle times factor through one of the eight actual product four-node faces. -/
theorem middle_support (r t : unitInterval) :
    ∃ (i : Fin 2) (j : Fin 4) (z : StdSimplex ℝ (Fin 4)),
      StdSimplex.map (middleEdgePairFace i j).toOrderHom z =
        BassMComponents.middleParameter.{u} (r, t) := by
  obtain ⟨i, z, hz⟩ := coefficient_path_in r
  obtain ⟨j, w, hw⟩ := BassH1Support.square_path_in t
  refine ⟨i, j, Quillen.SimplexGrid.parameter.{u + 1} 1 1 (z, w), ?_⟩
  rw [← parameter_middleEdgeProduct, hz, hw]
  rfl

end Quillen.PerfectComplexes.BassMPrimitiveSupport
