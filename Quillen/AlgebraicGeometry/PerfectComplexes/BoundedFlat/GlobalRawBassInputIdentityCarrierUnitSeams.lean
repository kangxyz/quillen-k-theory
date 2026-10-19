/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityCarrierTop
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityUnitBoundaryNodes
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityCarrierSeams

/-!
# Six exact unit and terminal joins in the original global identity carrier

Every equality is proved in the common codiscrete-nerve carrier from the complete actual reference
nodes. The bottom grid columns, contracted top boundary, and both original unit-square clocks
are preserved before evaluation. No native equality is inverted to obtain a carrier equality.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputIdentityCarrierUnitSeams

private theorem parameter_nodes {V W : Model.{u}} (F : V ⟶ W) {k l : ℕ}
    (N : Fin (k + 1) → CommonReferenceNerve.Node F)
    (M : Fin (l + 1) → CommonReferenceNerve.Node F) (α : ⦋l⦌ ⟶ ⦋k⦌)
    (h : ∀ i, N (α.toOrderHom i) = M i) (z : StdSimplex ℝ (Fin (l + 1))) :
    CommonReferenceNerve.parameter F N (StdSimplex.map α.toOrderHom z) =
      CommonReferenceNerve.parameter F M z := by
  rw [CommonReferenceNerve.parameter_face, funext h]

private theorem binary_parameters {V W : Model.{u}} (F : V ⟶ W) {k l : ℕ}
    (N : Fin (k + 1) → CommonReferenceNerve.Node F)
    (M : Fin (l + 1) → CommonReferenceNerve.Node F)
    (α : ⦋2⦌ ⟶ ⦋k⦌) (β : ⦋2⦌ ⟶ ⦋l⦌)
    (h : ∀ i, N (α.toOrderHom i) = M (β.toOrderHom i)) (t : unitInterval) :
    CommonReferenceNerve.parameter F N
        (binaryPath (α.toOrderHom 0) (α.toOrderHom 1) (α.toOrderHom 2) t) =
      CommonReferenceNerve.parameter F M
        (binaryPath (β.toOrderHom 0) (β.toOrderHom 1) (β.toOrderHom 2) t) := by
  have e := CommonReferenceNerve.parameter_eq_of_face_nodes F M N β α h
    (binaryPath (k := 2) 0 1 2 t)
  rw [BassSupportOrder.map_any_binary, BassSupportOrder.map_any_binary] at e
  exact e

/-- The initial Laurent product column retains the whole actual projection parameter. -/
theorem bottom_zero (t : unitInterval) :
    InputIdentityCarrierBottom.parameter.{u} (0, t) =
      StdSimplex.map (Quillen.SimplexGrid.columnFace 4 2 0).toOrderHom
        (InputIdentityProjection.parameter t) := by
  change Quillen.SimplexGrid.parameter.{u + 1} 4 2
    (InputIdentityProjection.parameter t, binaryPath (k := 2) 0 1 2 0) = _
  rw [Path.source, Quillen.SimplexGrid.parameter_column]

/-- The terminal Laurent product column retains the exact original projection speed. -/
theorem bottom_one (t : unitInterval) :
    InputIdentityCarrierBottom.parameter.{u} (1, t) =
      StdSimplex.map (Quillen.SimplexGrid.columnFace 4 2 2).toOrderHom
        (InputIdentityProjection.parameter t) := by
  change Quillen.SimplexGrid.parameter.{u + 1} 4 2
    (InputIdentityProjection.parameter t, binaryPath (k := 2) 0 1 2 1) = _
  rw [Path.target, Quillen.SimplexGrid.parameter_column]

/-- The complete positive endpoint follows both original Laurent identity segments. -/
theorem bottom_left (r : unitInterval) :
    InputIdentityCarrierBottom.parameter.{u} (r, 0) = binaryPath (k := 14) 6 7 8 r := by
  change Quillen.SimplexGrid.parameter.{u + 1} 4 2
    (InputIdentityProjection.parameter 0, binaryPath (k := 2) 0 1 2 r) = _
  rw [Path.source, Quillen.SimplexGrid.parameter_row]
  exact map_binaryPath (Quillen.SimplexGrid.rowFace 4 2 2) 0 1 2 r

/-- The inverse endpoint uses its distinct original Laurent product row. -/
theorem bottom_right (r : unitInterval) :
    InputIdentityCarrierBottom.parameter.{u} (r, 1) = binaryPath (k := 14) 12 13 14 r := by
  change Quillen.SimplexGrid.parameter.{u + 1} 4 2
    (InputIdentityProjection.parameter 1, binaryPath (k := 2) 0 1 2 r) = _
  rw [Path.target, Quillen.SimplexGrid.parameter_row]
  exact map_binaryPath (Quillen.SimplexGrid.rowFace 4 2 4) 0 1 2 r

private def terminalFace : ⦋4⦌ ⟶ ⦋24⦌ :=
  SimplexCategory.Hom.mk ⟨![20, 21, 22, 23, 24], by decide⟩
private def rightUnitFace : ⦋2⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![2, 3, 7], by decide⟩
private def leftUnitFace : ⦋2⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![5, 6, 7], by decide⟩
private def bottomPlusFace : ⦋2⦌ ⟶ ⦋14⦌ :=
  SimplexCategory.Hom.mk ⟨![6, 7, 8], by decide⟩
private def bottomMinusFace : ⦋2⦌ ⟶ ⦋14⦌ :=
  SimplexCategory.Hom.mk ⟨![12, 13, 14], by decide⟩
private def topPlusFace : ⦋2⦌ ⟶ ⦋24⦌ :=
  SimplexCategory.Hom.mk ⟨![2, 3, 22], by decide⟩
private def topMinusFace : ⦋2⦌ ⟶ ⦋24⦌ :=
  SimplexCategory.Hom.mk ⟨![7, 8, 24], by decide⟩

variable (X : Scheme.{u})

/-- The entire bottom terminal edge is the actual unpaused projection carrier path. -/
theorem bottom_terminal :
    (InputIdentityCarrierBottom.face X).comp
        ⟨fun t : unitInterval ↦ (1, t), by fun_prop⟩ =
      (InputIdentityCarrierProjection.face X).comp
        ⟨fun t : unitInterval ↦ (0, t), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro t
  change CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityCarrierBottom.nodes X) (InputIdentityCarrierBottom.parameter.{u} (1, t)) =
    CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityCarrierProjection.nodes X) (InputIdentityProjection.parameter t)
  rw [bottom_one]
  exact parameter_nodes _ _ _ (Quillen.SimplexGrid.columnFace 4 2 2)
    (InputIdentityUnitBoundaryNodes.bottom_terminal_nodes X) _

/-- All five top terminal nodes are exactly the actual projection nodes, including references. -/
theorem terminal_nodes (i : Fin 5) :
    InputIdentityCarrierTop.nodes X (![20, 21, 22, 23, 24] i) =
      InputIdentityCarrierProjection.nodes X i := by
  fin_cases i
  · exact (InputIdentityCarrierTop.middle_nodes X 10).trans
      (InputIdentityUnitBoundaryNodes.middle_terminal_nodes X 0)
  · exact (InputIdentityCarrierTop.middle_nodes X 11).trans
      (InputIdentityUnitBoundaryNodes.middle_terminal_nodes X 1)
  · exact (InputIdentityCarrierTop.middle_nodes X 12).trans
      (InputIdentityUnitBoundaryNodes.middle_terminal_nodes X 2)
  · exact (InputIdentityCarrierTop.middle_nodes X 13).trans
      (InputIdentityUnitBoundaryNodes.middle_terminal_nodes X 3)
  · exact (InputIdentityCarrierTop.middle_nodes X 14).trans
      (InputIdentityUnitBoundaryNodes.middle_terminal_nodes X 4)

/-- Both contracted top pauses end at the same whole unpaused projection carrier path. -/
theorem top_terminal :
    (InputIdentityCarrierTop.face X).comp
        ⟨fun t : unitInterval ↦ (1, t), by fun_prop⟩ =
      (InputIdentityCarrierProjection.face X).comp
        ⟨fun t : unitInterval ↦ (1, t), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro t
  change CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityCarrierTop.nodes X)
      (CoefficientPolynomialSpanUnitTop.topParameter.{u} (1, t)) =
    CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityCarrierProjection.nodes X) (InputIdentityProjection.parameter t)
  rw [CoefficientPolynomialSpanUnitTop.top_one]
  have e := parameter_nodes (InputIdentityNodes.source X) (InputIdentityCarrierTop.nodes X)
    (InputIdentityCarrierProjection.nodes X) terminalFace (terminal_nodes X)
    (InputIdentityProjection.parameter t)
  rw [InputIdentityProjection.parameter, BassSupportOrder.map_two_binary] at e
  exact e

/-- The whole plus bottom join retains all actual node references and original unit times. -/
theorem bottom_plus :
    (InputIdentityCarrierBottom.face X).comp
        ⟨fun r : unitInterval ↦ (r, 0), by fun_prop⟩ =
      (InputIdentityCarrierCharts.chartFace X plus plus_projection).comp
        ⟨fun r : unitInterval ↦ (r, 0), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro r
  change CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityCarrierBottom.nodes X)
      (InputIdentityCarrierBottom.parameter.{u} (r, 0)) =
    CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityNodes.chartSideNodes X plus plus_projection)
      (OriginalUnitSquareSimplex.squareParameter (r, 0))
  rw [bottom_left, OriginalUnitSquareSupport.square_left_path]
  apply binary_parameters _ _ _ bottomPlusFace rightUnitFace ?_ r
  intro i
  fin_cases i
  · exact (InputIdentityUnitBoundaryNodes.plus_bottom_nodes X 0).symm.trans
      (InputIdentityUnitBoundaryNodes.plus_side_actual X 2)
  · exact (InputIdentityUnitBoundaryNodes.plus_bottom_nodes X 1).symm.trans
      (InputIdentityUnitBoundaryNodes.plus_side_actual X 3)
  · exact (InputIdentityUnitBoundaryNodes.plus_bottom_nodes X 2).symm.trans
      (InputIdentityUnitBoundaryNodes.plus_side_actual X 7)

/-- The whole minus bottom join retains all actual node references and original unit times. -/
theorem bottom_minus :
    (InputIdentityCarrierBottom.face X).comp
        ⟨fun r : unitInterval ↦ (r, 1), by fun_prop⟩ =
      (InputIdentityCarrierCharts.chartFace X minus minus_projection).comp
        ⟨fun r : unitInterval ↦ (r, 0), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro r
  change CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityCarrierBottom.nodes X)
      (InputIdentityCarrierBottom.parameter.{u} (r, 1)) =
    CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityNodes.chartSideNodes X minus minus_projection)
      (OriginalUnitSquareSimplex.squareParameter (r, 0))
  rw [bottom_right, OriginalUnitSquareSupport.square_left_path]
  apply binary_parameters _ _ _ bottomMinusFace rightUnitFace ?_ r
  intro i
  fin_cases i
  · exact (InputIdentityUnitBoundaryNodes.minus_bottom_nodes X 0).symm.trans
      (InputIdentityUnitBoundaryNodes.minus_side_actual X 2)
  · exact (InputIdentityUnitBoundaryNodes.minus_bottom_nodes X 1).symm.trans
      (InputIdentityUnitBoundaryNodes.minus_side_actual X 3)
  · exact (InputIdentityUnitBoundaryNodes.minus_bottom_nodes X 2).symm.trans
      (InputIdentityUnitBoundaryNodes.minus_side_actual X 7)

/-- The whole plus top join retains all actual node references and original unit times. -/
theorem top_plus :
    (InputIdentityCarrierTop.face X).comp
        ⟨fun r : unitInterval ↦ (r, 0), by fun_prop⟩ =
      (InputIdentityCarrierCharts.chartFace X plus plus_projection).comp
        ⟨fun r : unitInterval ↦ (r, 1), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro r
  change CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityCarrierTop.nodes X)
      (CoefficientPolynomialSpanUnitTop.topParameter.{u} (r, 0)) =
    CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityNodes.chartSideNodes X plus plus_projection)
      (OriginalUnitSquareSimplex.squareParameter (r, 1))
  rw [CoefficientPolynomialSpanUnitTop.top_left, OriginalUnitSquareSupport.square_right_path]
  apply binary_parameters _ _ _ topPlusFace leftUnitFace ?_ r
  intro i
  fin_cases i
  · exact (InputIdentityCarrierTop.plus_nodes X 2).trans
      ((InputIdentityUnitBoundaryNodes.plus_top_nodes X 0).symm.trans
        (InputIdentityUnitBoundaryNodes.plus_side_actual X 5))
  · exact (InputIdentityCarrierTop.plus_nodes X 3).trans
      ((InputIdentityUnitBoundaryNodes.plus_top_nodes X 1).symm.trans
        (InputIdentityUnitBoundaryNodes.plus_side_actual X 6))
  · exact (InputIdentityCarrierTop.plus_nodes X 7).trans
      ((InputIdentityUnitBoundaryNodes.plus_top_nodes X 2).symm.trans
        (InputIdentityUnitBoundaryNodes.plus_side_actual X 7))

/-- The whole minus top join retains all actual node references and original unit times. -/
theorem top_minus :
    (InputIdentityCarrierTop.face X).comp
        ⟨fun r : unitInterval ↦ (r, 1), by fun_prop⟩ =
      (InputIdentityCarrierCharts.chartFace X minus minus_projection).comp
        ⟨fun r : unitInterval ↦ (r, 1), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro r
  change CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityCarrierTop.nodes X)
      (CoefficientPolynomialSpanUnitTop.topParameter.{u} (r, 1)) =
    CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityNodes.chartSideNodes X minus minus_projection)
      (OriginalUnitSquareSimplex.squareParameter (r, 1))
  rw [CoefficientPolynomialSpanUnitTop.top_right, OriginalUnitSquareSupport.square_right_path]
  apply binary_parameters _ _ _ topMinusFace leftUnitFace ?_ r
  intro i
  fin_cases i
  · exact (InputIdentityCarrierTop.minus_nodes X 2).trans
      ((InputIdentityUnitBoundaryNodes.minus_top_nodes X 0).symm.trans
        (InputIdentityUnitBoundaryNodes.minus_side_actual X 5))
  · exact (InputIdentityCarrierTop.minus_nodes X 3).trans
      ((InputIdentityUnitBoundaryNodes.minus_top_nodes X 1).symm.trans
        (InputIdentityUnitBoundaryNodes.minus_side_actual X 6))
  · exact (InputIdentityCarrierTop.minus_nodes X 7).trans
      ((InputIdentityUnitBoundaryNodes.minus_top_nodes X 2).symm.trans
        (InputIdentityUnitBoundaryNodes.minus_side_actual X 7))

end Quillen.PerfectComplexes.GlobalRawBass.InputIdentityCarrierUnitSeams
