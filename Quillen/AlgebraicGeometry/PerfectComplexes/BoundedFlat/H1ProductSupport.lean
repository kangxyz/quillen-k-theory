/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SquarePathProductFaces

/-! Exact small-face coverage of the unchanged independently varying H1 product parameters. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Quillen.SimplexParameters Quillen.ParameterSupport
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH1Support

/--
The union of the images of the four one-simplex edges traversed by the native five-vertex square
path.
-/
def squareEdgeSupport : Set (StdSimplex ℝ (Fin 5)) :=
  {z | ∃ (i : Fin 4) (w : StdSimplex ℝ (Fin 2)), StdSimplex.map (edgeFace i).toOrderHom w = z}

/-- Every point of each original edge belongs to its actual one-simplex image. -/
theorem square_edge_in (i : Fin 4) :
    PathIn squareEdgeSupport (edge (edgeStart i) (edgeEnd i)) := by
  intro t
  refine ⟨i, edge 0 1 t, ?_⟩
  exact BassSupportOrder.map_any_edge (edgeFace i).toOrderHom 0 1 t

/-- The whole original square path uses exactly these four original edge images. -/
theorem square_path_in : PathIn squareEdgeSupport NativeSquareFiveSimplex.parameter :=
  path_trans (path_symm (path_trans (square_edge_in 0) (square_edge_in 1)))
    (path_trans (square_edge_in 2) (square_edge_in 3))

/-- Two independent original path values factor through one of the sixteen actual grid faces. -/
theorem square_product_support (s t : unitInterval) :
    ∃ (i j : Fin 4) (z : StdSimplex ℝ (Fin 4)),
      StdSimplex.map (edgePairFace i j).toOrderHom z =
        Quillen.SimplexGrid.parameter.{u} 4 4
          (NativeSquareFiveSimplex.parameter s, NativeSquareFiveSimplex.parameter t) := by
  obtain ⟨i, z, hz⟩ := square_path_in s
  obtain ⟨j, w, hw⟩ := square_path_in t
  refine ⟨i, j, Quillen.SimplexGrid.parameter.{u} 1 1 (z, w), ?_⟩
  rw [← parameter_edgeProduct, hz, hw]

/-- Every positive H1 product value lies in an actual four-vertex face of its own diagram. -/
theorem plus_support (s t : unitInterval) :
    ∃ (i j : Fin 4) (z : StdSimplex ℝ (Fin 4)),
      StdSimplex.map (edgePairFace i j).toOrderHom z = BassH1Components.plusParameter.{u} (s, t) :=
  square_product_support.{u + 1} t s

/-- The inverse product has the same exact support while retaining its literal time reversal. -/
theorem minus_support (s t : unitInterval) :
    ∃ (i j : Fin 4) (z : StdSimplex ℝ (Fin 4)),
      StdSimplex.map (edgePairFace i j).toOrderHom z = BassH1Components.minusParameter.{u} (s, t) :=
  square_product_support.{u + 1} (unitInterval.symm t) s

end Quillen.PerfectComplexes.BassH1Support
