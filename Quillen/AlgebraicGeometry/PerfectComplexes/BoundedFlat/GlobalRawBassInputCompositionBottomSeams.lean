/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionBottomNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassBottomScalarEdge
public import Quillen.Topology.Realization.SimplexGridBoundary

/-!
# Whole original bottom/chart carrier seams for global input composition

The six complete dependent node identifications give the two entire carrier edges with their
original Laurent-composition clocks. These are equalities in the actual common-reference nerve,
not only equalities after native evaluation.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionBottomSeams

/-- The actual last Laurent triangle in either original chart rectangle. -/
def chartEdge : ⦋2⦌ ⟶ ⦋17⦌ := SimplexCategory.Hom.mk ⟨![15, 16, 17], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The positive endpoint row of the original five-by-three product. -/
def plusEdge : ⦋2⦌ ⟶ ⦋14⦌ := SimplexCategory.Hom.mk ⟨![6, 7, 8], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The inverse endpoint row of that same original product. -/
def minusEdge : ⦋2⦌ ⟶ ⦋14⦌ := SimplexCategory.Hom.mk ⟨![12, 13, 14], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The whole positive bottom boundary has its exact original split-composition speed. -/
theorem parameter_plus (r : unitInterval) :
    InputCompositionCarrierBottom.parameter.{u} (r, 0) = binaryPath (k := 14) 6 7 8 r := by
  change Quillen.SimplexGrid.parameter.{u + 1} 4 2
    (InputIdentityProjection.parameter 0, binaryPath (k := 2) 0 1 2 r) = _
  rw [Path.source, Quillen.SimplexGrid.parameter_row]
  exact map_binaryPath (Quillen.SimplexGrid.rowFace 4 2 2) 0 1 2 r

/-- The whole inverse bottom boundary retains that same split-composition speed. -/
theorem parameter_minus (r : unitInterval) :
    InputCompositionCarrierBottom.parameter.{u} (r, 1) =
      binaryPath (k := 14) 12 13 14 r := by
  change Quillen.SimplexGrid.parameter.{u + 1} 4 2
    (InputIdentityProjection.parameter 1, binaryPath (k := 2) 0 1 2 r) = _
  rw [Path.target, Quillen.SimplexGrid.parameter_row]
  exact map_binaryPath (Quillen.SimplexGrid.rowFace 4 2 4) 0 1 2 r

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Every point of the actual positive seam agrees in the full-reference carrier. -/
theorem bottom_plus (r : unitInterval) :
    InputCompositionCarrierBottom.face f g (r, 0) =
      InputCompositionCarrierCharts.chartFace f g plus plus_projection (r, 0) := by
  change CommonReferenceNerve.parameter _ _
    (InputCompositionCarrierBottom.parameter.{u} (r, 0)) =
      CommonReferenceNerve.parameter _ _
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 0))
  rw [parameter_plus, DoubleSquareScalarPaths.coefficientPausedSquareParameter_left]
  have h := CommonReferenceNerve.parameter_eq_of_face_nodes
    (InputCompositionCarrierCharts.source f g)
    (InputCompositionCarrierBottom.nodes f g)
    (InputCompositionCarrierCharts.chartNodes f g plus plus_projection)
    plusEdge chartEdge (fun i ↦ ?_) (binaryPath (k := 2) 0 1 2 r)
  · have hc : StdSimplex.map chartEdge.toOrderHom (binaryPath (k := 2) 0 1 2 r) =
        DoubleSquareScalarPaths.targetChart r := map_binaryPath chartEdge 0 1 2 r
    have hb : StdSimplex.map plusEdge.toOrderHom (binaryPath (k := 2) 0 1 2 r) =
        binaryPath (k := 14) 6 7 8 r := map_binaryPath plusEdge 0 1 2 r
    exact (congrArg (CommonReferenceNerve.parameter (InputCompositionCarrierCharts.source f g)
      (InputCompositionCarrierBottom.nodes f g)) hb).symm.trans
      (h.symm.trans (congrArg
        (CommonReferenceNerve.parameter (InputCompositionCarrierCharts.source f g)
          (InputCompositionCarrierCharts.chartNodes f g plus plus_projection)) hc))
  · fin_cases i
    · exact InputCompositionBottomNodes.plus_source_node f g
    · exact InputCompositionBottomNodes.plus_intermediate_node f g
    · exact InputCompositionBottomNodes.plus_target_node f g

/-- Every point of the inverse seam agrees, including its original distinct source transport. -/
theorem bottom_minus (r : unitInterval) :
    InputCompositionCarrierBottom.face f g (r, 1) =
      InputCompositionCarrierCharts.chartFace f g minus minus_projection (r, 0) := by
  change CommonReferenceNerve.parameter _ _
    (InputCompositionCarrierBottom.parameter.{u} (r, 1)) =
      CommonReferenceNerve.parameter _ _
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 0))
  rw [parameter_minus, DoubleSquareScalarPaths.coefficientPausedSquareParameter_left]
  have h := CommonReferenceNerve.parameter_eq_of_face_nodes
    (InputCompositionCarrierCharts.source f g)
    (InputCompositionCarrierBottom.nodes f g)
    (InputCompositionCarrierCharts.chartNodes f g minus minus_projection)
    minusEdge chartEdge (fun i ↦ ?_) (binaryPath (k := 2) 0 1 2 r)
  · have hc : StdSimplex.map chartEdge.toOrderHom (binaryPath (k := 2) 0 1 2 r) =
        DoubleSquareScalarPaths.targetChart r := map_binaryPath chartEdge 0 1 2 r
    have hb : StdSimplex.map minusEdge.toOrderHom (binaryPath (k := 2) 0 1 2 r) =
        binaryPath (k := 14) 12 13 14 r := map_binaryPath minusEdge 0 1 2 r
    exact (congrArg (CommonReferenceNerve.parameter (InputCompositionCarrierCharts.source f g)
      (InputCompositionCarrierBottom.nodes f g)) hb).symm.trans
      (h.symm.trans (congrArg
        (CommonReferenceNerve.parameter (InputCompositionCarrierCharts.source f g)
          (InputCompositionCarrierCharts.chartNodes f g minus minus_projection)) hc))
  · fin_cases i
    · exact InputCompositionBottomNodes.minus_source_node f g
    · exact InputCompositionBottomNodes.minus_intermediate_node f g
    · exact InputCompositionBottomNodes.minus_target_node f g

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionBottomSeams
