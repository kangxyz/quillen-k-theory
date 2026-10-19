/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionBottomSeams

/-! Whole dependent-node families and original carrier-edge clocks for the two bottom seams. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.PerfectComplexes.GlobalRawBass
universe u
namespace QuillenTest.GlobalRawBassInputCompositionBottomSeams
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The entire positive common triangle agrees as a family of full dependent nodes. -/
theorem plus_node_family :
    (fun i : Fin 3 ↦ InputCompositionCarrierCharts.chartNodes f g plus plus_projection
      (InputCompositionBottomSeams.chartEdge.toOrderHom i)) =
    (fun i : Fin 3 ↦ InputCompositionCarrierBottom.nodes f g
      (InputCompositionBottomSeams.plusEdge.toOrderHom i)) := by
  funext i
  fin_cases i
  · exact InputCompositionBottomNodes.plus_source_node f g
  · exact InputCompositionBottomNodes.plus_intermediate_node f g
  · exact InputCompositionBottomNodes.plus_target_node f g

/-- The inverse common triangle retains its separate chosen source transport in the family. -/
theorem minus_node_family :
    (fun i : Fin 3 ↦ InputCompositionCarrierCharts.chartNodes f g minus minus_projection
      (InputCompositionBottomSeams.chartEdge.toOrderHom i)) =
    (fun i : Fin 3 ↦ InputCompositionCarrierBottom.nodes f g
      (InputCompositionBottomSeams.minusEdge.toOrderHom i)) := by
  funext i
  fin_cases i
  · exact InputCompositionBottomNodes.minus_source_node f g
  · exact InputCompositionBottomNodes.minus_intermediate_node f g
  · exact InputCompositionBottomNodes.minus_target_node f g

/-- The actual positive carrier paths agree as whole functions, not only at selected times. -/
theorem plus_path :
    (fun r : unitInterval ↦ InputCompositionCarrierBottom.face f g (r, 0)) =
      (fun r : unitInterval ↦
        InputCompositionCarrierCharts.chartFace f g plus plus_projection (r, 0)) :=
  funext (InputCompositionBottomSeams.bottom_plus f g)

/-- The original inverse boundary also agrees at every unchanged composition time. -/
theorem minus_path :
    (fun r : unitInterval ↦ InputCompositionCarrierBottom.face f g (r, 1)) =
      (fun r : unitInterval ↦
        InputCompositionCarrierCharts.chartFace f g minus minus_projection (r, 0)) :=
  funext (InputCompositionBottomSeams.bottom_minus f g)

end QuillenTest.GlobalRawBassInputCompositionBottomSeams
