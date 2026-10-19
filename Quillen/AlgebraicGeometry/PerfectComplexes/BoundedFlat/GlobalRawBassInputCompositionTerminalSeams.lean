/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionTerminalRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0ScalarEdges
public import Quillen.Topology.Realization.SimplexGridBoundary

/-!
# Both whole original product/middle terminal seams

The two complete original five-node chart paths agree in the common reference carrier.
Their product-row clocks and original input-boundary clocks are retained before evaluation.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTerminalSeams

/-- The five original positive input-chart nodes form their actual ordered face. -/
def plusEdge : ⦋4⦌ ⟶ ⦋30⦌ := SimplexCategory.Hom.mk
  ⟨fun i ↦ BassH0Diagram.plusFace.toOrderHom (ProjectionRectangleSquareRows.chartRow i), by
    decide⟩

/-- The distinct inverse input-chart row retains its actual original position. -/
def minusEdge : ⦋4⦌ ⟶ ⦋30⦌ := SimplexCategory.Hom.mk
  ⟨fun i ↦ BassH0Diagram.minusFace.toOrderHom (ProjectionRectangleSquareRows.chartRow i), by
    decide⟩

/-- The whole positive edge keeps the native original five-node square path. -/
theorem plus_parameter (s : unitInterval) :
    StdSimplex.map plusEdge.toOrderHom (NativeSquareFiveSimplex.parameter s) =
      BassH0Diagram.parameter (s, 0) := by
  rw [BassH0Diagram.parameter_left]
  exact ProjectionRectangleSquareRows.chart_parameter BassH0Diagram.plusFace s

/-- The separate inverse edge keeps its own full original square path. -/
theorem minus_parameter (s : unitInterval) :
    StdSimplex.map minusEdge.toOrderHom (NativeSquareFiveSimplex.parameter s) =
      BassH0Diagram.parameter (s, 1) := by
  rw [BassH0Diagram.parameter_right]
  exact ProjectionRectangleSquareRows.chart_parameter BassH0Diagram.minusFace s

/-- The actual final polynomial row has exactly the old independent product clock. -/
theorem product_parameter (s : unitInterval) :
    StdSimplex.map (Quillen.SimplexGrid.rowFace 4 4 4).toOrderHom
      (NativeSquareFiveSimplex.parameter s) =
        InputCompositionTerminalProducts.parameter.{u} (s, 1) := by
  change _ = Quillen.SimplexGrid.parameter.{u + 1} 4 4
    (NativeSquareFiveSimplex.parameter 1, NativeSquareFiveSimplex.parameter s)
  rw [Path.target]
  exact (Quillen.SimplexGrid.parameter_row 4 4 4 _).symm

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The entire positive product endpoint equals the original middle source in the carrier. -/
theorem plus_middle (s : unitInterval) :
    InputCompositionTerminalProducts.face f g plus plus_projection (s, 1) =
      InputCompositionTerminalAttach.preFace f g (s, 0) := by
  change CommonReferenceNerve.parameter _ _
    (InputCompositionTerminalProducts.parameter.{u} (s, 1)) =
    CommonReferenceNerve.mapParameter (InputCompositionTerminalAttach.preNode f g)
      (CommonReferenceNerve.parameter (InputDescSimplex.reference f) (InputDescSimplex.nodes f)
        (BassH0Diagram.parameter (s, 0)))
  rw [CommonReferenceNerve.mapParameter_parameter]
  have h := CommonReferenceNerve.parameter_eq_of_face_nodes
    (InputCompositionCarrierCharts.source f g)
    (InputCompositionTerminalProducts.nodes f g plus plus_projection)
    (fun i ↦ InputCompositionTerminalAttach.preNode f g (InputDescSimplex.nodes f i))
    (Quillen.SimplexGrid.rowFace 4 4 4) plusEdge
    (fun i ↦ (congrArg (InputCompositionTerminalAttach.preNode f g)
      (InputDescSimplex.plus_nodes f (ProjectionRectangleSquareRows.chartRow i))).trans
        (InputCompositionTerminalRows.row_nodes f g plus plus_projection i))
    (NativeSquareFiveSimplex.parameter s)
  exact (congrArg (CommonReferenceNerve.parameter (InputCompositionCarrierCharts.source f g)
    (InputCompositionTerminalProducts.nodes f g plus plus_projection))
      (product_parameter.{u} s)).symm.trans
    (h.symm.trans (congrArg (CommonReferenceNerve.parameter
      (InputCompositionCarrierCharts.source f g)
      (fun i ↦ InputCompositionTerminalAttach.preNode f g (InputDescSimplex.nodes f i)))
        (plus_parameter s)))

/-- The entire inverse product endpoint equals the original distinct middle target. -/
theorem minus_middle (s : unitInterval) :
    InputCompositionTerminalProducts.face f g minus minus_projection (s, 1) =
      InputCompositionTerminalAttach.preFace f g (s, 1) := by
  change CommonReferenceNerve.parameter _ _
    (InputCompositionTerminalProducts.parameter.{u} (s, 1)) =
    CommonReferenceNerve.mapParameter (InputCompositionTerminalAttach.preNode f g)
      (CommonReferenceNerve.parameter (InputDescSimplex.reference f) (InputDescSimplex.nodes f)
        (BassH0Diagram.parameter (s, 1)))
  rw [CommonReferenceNerve.mapParameter_parameter]
  have h := CommonReferenceNerve.parameter_eq_of_face_nodes
    (InputCompositionCarrierCharts.source f g)
    (InputCompositionTerminalProducts.nodes f g minus minus_projection)
    (fun i ↦ InputCompositionTerminalAttach.preNode f g (InputDescSimplex.nodes f i))
    (Quillen.SimplexGrid.rowFace 4 4 4) minusEdge
    (fun i ↦ (congrArg (InputCompositionTerminalAttach.preNode f g)
      (InputDescSimplex.minus_nodes f (ProjectionRectangleSquareRows.chartRow i))).trans
        (InputCompositionTerminalRows.row_nodes f g minus minus_projection i))
    (NativeSquareFiveSimplex.parameter s)
  exact (congrArg (CommonReferenceNerve.parameter (InputCompositionCarrierCharts.source f g)
    (InputCompositionTerminalProducts.nodes f g minus minus_projection))
      (product_parameter.{u} s)).symm.trans
    (h.symm.trans (congrArg (CommonReferenceNerve.parameter
      (InputCompositionCarrierCharts.source f g)
      (fun i ↦ InputCompositionTerminalAttach.preNode f g (InputDescSimplex.nodes f i)))
        (minus_parameter s)))

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTerminalSeams
