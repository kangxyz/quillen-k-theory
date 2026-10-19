/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentitySeedLaurentSeams
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentitySeedPolynomialFaces

/-! Whole actual chart edges, including their full polynomial attachment on each sheet. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputIdentitySeedChartSeams
open CommonReferenceNerve InputIdentitySeedCarrier InputIdentitySeedLaurentFaces
open InputIdentitySeedLaurentSeams
variable (X : Scheme.{u})

/-- The whole original plus comparison is the initial chart edge before evaluation. -/
theorem chart_initial (e : Bool) (s : I) :
    chartFace X e (0, s) = InputIdentitySeedRectangle.positiveMovement (𝟙 X) e s := by
  have h := congrArg (sheet X e)
    (DFunLike.congr_fun (InputIdentityCarrierSeams.plus_seam X) s)
  change sheet X e (parameter (InputIdentityNodes.source X) (InputIdentityNodes.nodes X)
    (BassH0Diagram.parameter (s, 0))) = chartFace X e (0, s) at h
  rw [BassH0Diagram.parameter_left] at h
  exact h.symm.trans (sheet_raw X e (ProjectionRectangleParameters.L BassH0Diagram.plusFace s))

/-- The entire terminal chart edge is one full reference point, with no added path segment. -/
theorem chart_terminal (e : Bool) (s : I) :
    chartFace X e (1, s) = chartFace X e (1, 0) := by
  change sheet X e (parameter _ _ (OriginalUnitSquareSimplex.squareParameter (1, s))) =
    sheet X e (parameter _ _ (OriginalUnitSquareSimplex.squareParameter (1, 0)))
  rw [OriginalUnitSquareSupport.square_top_path, OriginalUnitSquareSupport.square_top_path]

private def leftUnitFace : ⦋2⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![5, 6, 7], by decide⟩
private def rightUnitFace : ⦋2⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![2, 3, 7], by decide⟩

/-- The full chart edge is attached to the original polynomial identity rail on each sheet. -/
theorem chart_polynomial (e : Bool) (r : I) :
    chartFace X e (r, 1) = InputIdentitySeedCone.cylinder (𝟙 X) e
      (InputIdentitySeedPolynomialFaces.targetRail X r, 0) := by
  rw [show InputIdentitySeedPolynomialFaces.targetRail X r =
    parameter (polyRef (𝟙 X)) (InputIdentitySeedPolynomialFaces.K X)
      (binaryPath (k := 7) 2 3 7 r) from rfl,
    InputIdentitySeedPolynomialFaces.cylinder_zero]
  change sheet X e (parameter _ _ (OriginalUnitSquareSimplex.squareParameter (r, 1))) = _
  rw [OriginalUnitSquareSupport.square_right_path]
  apply congrArg (sheet X e)
  have h := parameter_eq_of_face_nodes (InputIdentityNodes.source X)
    (InputIdentityTopNodes.plusNodes X)
    (InputIdentityNodes.chartSideNodes X plus plus_projection)
    rightUnitFace leftUnitFace (fun i ↦ ?_) (binaryPath (k := 2) 0 1 2 r)
  · rw [BassSupportOrder.map_any_binary, BassSupportOrder.map_any_binary] at h
    exact h
  · exact (InputIdentityUnitBoundaryNodes.plus_side_actual X (leftUnitFace.toOrderHom i)).symm.trans
      (InputIdentityUnitBoundaryNodes.plus_top_nodes X i)

end Quillen.PerfectComplexes.GlobalRawBass.InputIdentitySeedChartSeams
