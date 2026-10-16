/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPauseAttachments

/-!
# Literal product-pause outer surfaces and their actual edge attachments

These faces retain the original ninety-node families, with fixed-factor eighteen-node
characteristic maps and their full anchors. No transfer into the old 140-node interior
is asserted. The changing Pc seam and fixed Pl seam retain distinct time coordinates.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeNerve
open BassReferenceMerge BassH0Merge BassH1Join

/-- Original square endpoint time, independent of pause and coefficient times. -/
def productEndpointTime (e : Fin 2) : unitInterval := ![0, 1] e

private theorem square_parameter_endpoint (e : Fin 2) :
    NativeSquareFiveSimplex.parameter (productEndpointTime e) =
      StdSimplex.single (productSquareEndpoint e) := by
  fin_cases e <;> simp [productEndpointTime, productSquareEndpoint, Path.source, Path.target]

/-- The inverse orientation changes only the original polynomial coordinate. -/
def productOuterTime (inverse : Bool) (e : Fin 2) : unitInterval :=
  productPolynomialTime inverse (productEndpointTime e)

private theorem polynomial_outer_time (inverse : Bool) (e : Fin 2) :
    productPolynomialTime inverse (productOuterTime inverse e) = productEndpointTime e := by
  cases inverse <;> simp [productOuterTime, productPolynomialTime]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- The full fixed-factor reference family; no new reference is chosen. -/
def polynomialOuterNodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (e : Fin 2) := fun i : Fin 18 ↦
  postReferenceNode _
    (CoefficientSquareFamilies.chartNodes P w α (productSquareEndpoint e)).1
    (polynomialFixedSideAnchor P u v w α hc e)
    (movingSquareNodes P (polynomialUnderCoefficient R) u v i)

/-- A literal outer surface, evaluated only in its original fixed-factor family. -/
def polynomialOuterSurface
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (e : Fin 2) : C(Quillen.SimplexCubeExtension.Cube,
      |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|) :=
  (CommonReferenceNerve.parameter _ (polynomialOuterNodes P u v w α hc e)).comp
    coefficientPauseCube

/-- The full fixed-factor reference family; no new reference is chosen. -/
def chartOuterNodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (e : Fin 2) := fun i : Fin 18 ↦
  preReferenceNode _
    (CoefficientSquareFamilies.polynomialNodes P u (productSquareEndpoint e)).1
    (chartFixedSideAnchor P u v w α hd e) (movingSquareNodes P α v w i)

/-- A literal outer surface, evaluated only in its original fixed-factor family. -/
def chartOuterSurface
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (e : Fin 2) : C(Quillen.SimplexCubeExtension.Cube,
      |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|) :=
  (CommonReferenceNerve.parameter _ (chartOuterNodes P u v w α hd e)).comp
    coefficientPauseCube

/-- The ordered whole column identity holds for every scalar point, without support assumptions. -/
theorem polynomial_outer_parameter
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (e : Fin 2) (z : StdSimplex ℝ (Fin 18)) :
    CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w α hc)
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (z, StdSimplex.single (productSquareEndpoint e))) =
    CommonReferenceNerve.parameter _ (polynomialOuterNodes P u v w α hc e) z := by
  refine ((congrArg (CommonReferenceNerve.parameter _
    (polynomialProductNodes P u v w α hc))
    (Quillen.SimplexGrid.parameter_column.{u + 1} 17 4 (productSquareEndpoint e) z)).trans
      (CommonReferenceNerve.parameter_face _ (polynomialProductNodes P u v w α hc)
        (Quillen.SimplexGrid.columnFace 17 4 (productSquareEndpoint e)) z)).trans ?_
  apply congrArg (fun N : Fin 18 → CommonReferenceNerve.Node
    (BassH0Diagram.reference P ((u ≫ v) ≫ w)) ↦ CommonReferenceNerve.parameter _ N z)
  funext i
  exact polynomial_fixed_side_nodes P u v w α hc e i

/-- The ordered whole row identity is valid for every scalar point, without support assumptions. -/
theorem chart_outer_parameter
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (e : Fin 2) (z : StdSimplex ℝ (Fin 18)) :
    CommonReferenceNerve.parameter _ (chartProductNodes P u v w α hd)
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (StdSimplex.single (productSquareEndpoint e), z)) =
    CommonReferenceNerve.parameter _ (chartOuterNodes P u v w α hd e) z := by
  refine ((congrArg (CommonReferenceNerve.parameter _
    (chartProductNodes P u v w α hd))
    (Quillen.SimplexGrid.parameter_row.{u + 1} 4 17 (productSquareEndpoint e) z)).trans
      (CommonReferenceNerve.parameter_face _ (chartProductNodes P u v w α hd)
        (Quillen.SimplexGrid.rowFace 4 17 (productSquareEndpoint e)) z)).trans ?_
  apply congrArg (fun N : Fin 18 → CommonReferenceNerve.Node
    (BassH0Diagram.reference P ((u ≫ v) ≫ w)) ↦ CommonReferenceNerve.parameter _ N z)
  funext i
  exact chart_fixed_side_nodes P u v w α hd e i

/-- Both polynomial outer surfaces, with the original inverse time left visible. -/
theorem polynomial_pause_outer_face
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (e : Fin 2) (r q t : unitInterval) :
    polynomialPause P u v w α hc inverse ![r, q, productEndpointTime e, t] =
      polynomialOuterSurface P u v w α hc e
        ![r, q, productPolynomialTime inverse t] := by
  change CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w α hc)
    (Quillen.SimplexGrid.parameter.{u + 1} 17 4
      (coefficientPauseCube ![r, q, productPolynomialTime inverse t],
        NativeSquareFiveSimplex.parameter (productEndpointTime e))) = _
  rw [square_parameter_endpoint, polynomial_outer_parameter]
  rfl

/-- Both chart outer surfaces; the inverse mode swaps only the physical polynomial endpoint. -/
theorem chart_pause_outer_face
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (e : Fin 2) (r q s : unitInterval) :
    chartPause P u v w α hd inverse ![r, q, s, productOuterTime inverse e] =
      chartOuterSurface P u v w α hd e ![r, q, s] := by
  change CommonReferenceNerve.parameter _ (chartProductNodes P u v w α hd)
    (Quillen.SimplexGrid.parameter.{u + 1} 4 17
      (NativeSquareFiveSimplex.parameter
        (productPolynomialTime inverse (productOuterTime inverse e)),
        coefficientPauseCube ![r, q, s])) = _
  rw [polynomial_outer_time, square_parameter_endpoint, chart_outer_parameter]
  rfl

/-- Initial outer face is exactly the corresponding old ninety-node product edge. -/
theorem polynomial_outer_zero
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (e : Fin 2) (q t : unitInterval) :
    polynomialOuterSurface P u v w α hc e ![0, q, productPolynomialTime inverse t] =
      polynomialProductPrism P u v w α hc inverse ![q, productEndpointTime e, t] := by
  rw [← polynomial_pause_outer_face P u v w α hc inverse e 0 q t]
  exact polynomial_pause_zero P u v w α hc inverse q _ _

/-- Initial outer face is exactly the corresponding old ninety-node product edge. -/
theorem chart_outer_zero
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (e : Fin 2) (q s : unitInterval) :
    chartOuterSurface P u v w α hd e ![0, q, s] =
      chartProductPrism P u v w α hd inverse ![q, s, productOuterTime inverse e] := by
  rw [← chart_pause_outer_face P u v w α hd inverse e 0 q s]
  exact chart_pause_zero P u v w α hd inverse q _ _

/-- The raw chart-source outer edge has the actual changed coefficient time. -/
theorem chart_outer_source
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (e : Fin 2) (r q : unitInterval) :
    chartOuterSurface P u v w α hd e ![r, q, 1] =
      chartProductPrism P u v w α hd inverse
        ![ChangedBoundaryPause.time (r, q), 1, productOuterTime inverse e] := by
  rw [← chart_pause_outer_face P u v w α hd inverse e r q 1]
  exact chart_pause_source_side P u v w α hd inverse r q _

/-- Actual changing Pc edge of each polynomial outer surface. -/
theorem polynomial_outer_plus_coefficient_edge (e : Fin 2) (r q : unitInterval) :
    polynomialOuterSurface P u v w (underToLaurent R) (laurentPlus_projection P c) e ![r, q, 1] =
      coefficientPrismPause P u v w ![r, q, productEndpointTime e, 0] := by
  have h := polynomial_pause_outer_face P u v w (underToLaurent R)
    (laurentPlus_projection P c) false e r q 1
  have ht : productPolynomialTime false 1 = 1 := rfl
  exact (congrArg (fun t : unitInterval ↦ polynomialOuterSurface P u v w
    (underToLaurent R) (laurentPlus_projection P c) e ![r, q, t]) ht).symm.trans
      (h.symm.trans (polynomial_pause_plus_coefficient_seam P u v w r q _))

/-- Actual changing Pc edge of each polynomial outer surface. -/
theorem polynomial_outer_minus_coefficient_edge (e : Fin 2) (r q : unitInterval) :
    polynomialOuterSurface P u v w (underToLaurentInvert R) (laurentMinus_projection P c) e
      ![r, q, 1] =
      coefficientPrismPause P u v w ![r, q, productEndpointTime e, 1] := by
  have h := polynomial_pause_outer_face P u v w (underToLaurentInvert R)
    (laurentMinus_projection P c) true e r q 0
  have ht : productPolynomialTime true 0 = 1 := by
    change unitInterval.symm 0 = 1
    exact unitInterval.symm_zero
  exact (congrArg (fun t : unitInterval ↦ polynomialOuterSurface P u v w
    (underToLaurentInvert R) (laurentMinus_projection P c) e ![r, q, t]) ht).symm.trans
      (h.symm.trans (polynomial_pause_minus_coefficient_seam P u v w r q _))

/-- Actual fixed Pl top edge, with its original subinterval coordinate. -/
theorem chart_outer_plus_laurent_edge (e : Fin 2) (r q : unitInterval) :
    chartOuterSurface P u v w (underToLaurent R) (laurentPlus_projection P d) e ![r, q, 0] =
      laurentPrism P u v w ![q, 1, lower (productOuterTime false e)] := by
  rw [← chart_pause_outer_face P u v w (underToLaurent R)
    (laurentPlus_projection P d) false e r q 0]
  exact chart_pause_plus_laurent_seam P u v w r q _

/-- Actual fixed Pl top edge, with its original subinterval coordinate. -/
theorem chart_outer_minus_laurent_edge (e : Fin 2) (r q : unitInterval) :
    chartOuterSurface P u v w (underToLaurentInvert R) (laurentMinus_projection P d) e ![r, q, 0] =
      laurentPrism P u v w ![q, 1, upper (upper (productOuterTime true e))] := by
  rw [← chart_pause_outer_face P u v w (underToLaurentInvert R)
    (laurentMinus_projection P d) true e r q 0]
  exact chart_pause_minus_laurent_seam P u v w r q _

/-- All six scalar boundary restrictions, including both q endpoints and the terminal
pauseRight face, are inherited literally under the same fixed-factor characteristic map. -/
theorem polynomial_outer_boundary
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (e : Fin 2) (x : Quillen.SimplexCubeExtension.boundary) :
    polynomialOuterSurface P u v w α hc e x.val =
      CommonReferenceNerve.parameter _ (polynomialOuterNodes P u v w α hc e)
        (ChangedBoundaryPause.boundaryMap
          DoubleSquareScalarPaths.coefficientBoundaryParameter x) := by
  change CommonReferenceNerve.parameter _ (polynomialOuterNodes P u v w α hc e)
    (ChangedBoundaryPause.cube DoubleSquareScalarPaths.coefficientBoundaryParameter x.val) = _
  rw [ChangedBoundaryPause.cube_boundary]

/-- All six scalar boundary restrictions, including both q endpoints and the terminal
pauseRight face, are inherited literally under the same fixed-factor characteristic map. -/
theorem chart_outer_boundary
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (e : Fin 2) (x : Quillen.SimplexCubeExtension.boundary) :
    chartOuterSurface P u v w α hd e x.val =
      CommonReferenceNerve.parameter _ (chartOuterNodes P u v w α hd e)
        (ChangedBoundaryPause.boundaryMap
          DoubleSquareScalarPaths.coefficientBoundaryParameter x) := by
  change CommonReferenceNerve.parameter _ (chartOuterNodes P u v w α hd e)
    (ChangedBoundaryPause.cube DoubleSquareScalarPaths.coefficientBoundaryParameter x.val) = _
  rw [ChangedBoundaryPause.cube_boundary]

end Quillen.PerfectComplexes.BassMWholeNerve
