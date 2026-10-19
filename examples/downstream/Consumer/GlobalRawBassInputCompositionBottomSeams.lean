/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionBottomSeams

/-! Independent consumers of both whole carrier seams and their complete reference families. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.PerfectComplexes.GlobalRawBass
universe u
namespace Consumer.GlobalRawBassInputCompositionBottomSeams
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The two original boundary paths agree simultaneously, retaining the two different heights. -/
theorem simultaneous_edges :
    (fun r : unitInterval ↦
      (InputCompositionCarrierBottom.face f g (r, 0),
        InputCompositionCarrierBottom.face f g (r, 1))) =
    (fun r : unitInterval ↦
      (InputCompositionCarrierCharts.chartFace f g plus plus_projection (r, 0),
        InputCompositionCarrierCharts.chartFace f g minus minus_projection (r, 0))) := by
  funext r
  exact Prod.ext (InputCompositionBottomSeams.bottom_plus f g r)
    (InputCompositionBottomSeams.bottom_minus f g r)

/-- Both final normalization nodes agree before any native evaluation or homotopy quotient. -/
theorem simultaneous_target_nodes :
    (InputCompositionCarrierCharts.chartNodes f g plus plus_projection 17,
      InputCompositionCarrierCharts.chartNodes f g minus minus_projection 17) =
    (InputCompositionCarrierBottom.nodes f g 8, InputCompositionCarrierBottom.nodes f g 14) :=
  Prod.ext (InputCompositionBottomNodes.plus_target_node f g)
    (InputCompositionBottomNodes.minus_target_node f g)

end Consumer.GlobalRawBassInputCompositionBottomSeams
