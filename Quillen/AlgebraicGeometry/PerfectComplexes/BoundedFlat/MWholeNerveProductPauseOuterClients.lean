/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPauseOuterEndpoints

/-!
# Strict semantic consumers of the literal outer surfaces and endpoint joins

All statements retain the actual whole maps and specified references. The four physical
outer faces have separate named consumers in addition to the parameterized edge consumers.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeNerve.OuterFaceClients
open BassReferenceMerge BassH0Merge BassH1Join

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- Exact named whole-map consumer. -/
theorem client_polynomial_outer_parameter
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (e : Fin 2) (z : StdSimplex ℝ (Fin 18)) :
    CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w α hc)
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (z, StdSimplex.single (productSquareEndpoint e))) =
    CommonReferenceNerve.parameter _ (polynomialOuterNodes P u v w α hc e) z := by
  exact BassMWholeNerve.polynomial_outer_parameter P u v w α hc e z

/-- Exact named whole-map consumer. -/
theorem client_chart_outer_parameter
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (e : Fin 2) (z : StdSimplex ℝ (Fin 18)) :
    CommonReferenceNerve.parameter _ (chartProductNodes P u v w α hd)
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (StdSimplex.single (productSquareEndpoint e), z)) =
    CommonReferenceNerve.parameter _ (chartOuterNodes P u v w α hd e) z := by
  exact BassMWholeNerve.chart_outer_parameter P u v w α hd e z

/-- Exact named whole-map consumer. -/
theorem client_polynomial_pause_outer_face
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (e : Fin 2) (r q t : unitInterval) :
    polynomialPause P u v w α hc inverse ![r, q, productEndpointTime e, t] =
      polynomialOuterSurface P u v w α hc e
        ![r, q, productPolynomialTime inverse t] := by
  exact BassMWholeNerve.polynomial_pause_outer_face P u v w α hc inverse e r q t

/-- One distinct fixed physical-factor face, with inverse time explicit. -/
theorem client_polynomial_pause_outer_face_0
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (r q t : unitInterval) :
    polynomialPause P u v w α hc inverse ![r, q, productEndpointTime 0, t] =
      polynomialOuterSurface P u v w α hc 0
        ![r, q, productPolynomialTime inverse t] := by
  exact BassMWholeNerve.polynomial_pause_outer_face P u v w α hc inverse 0 r q t

/-- One distinct fixed physical-factor face, with inverse time explicit. -/
theorem client_polynomial_pause_outer_face_1
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (r q t : unitInterval) :
    polynomialPause P u v w α hc inverse ![r, q, productEndpointTime 1, t] =
      polynomialOuterSurface P u v w α hc 1
        ![r, q, productPolynomialTime inverse t] := by
  exact BassMWholeNerve.polynomial_pause_outer_face P u v w α hc inverse 1 r q t

/-- Exact named whole-map consumer. -/
theorem client_chart_pause_outer_face
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (e : Fin 2) (r q s : unitInterval) :
    chartPause P u v w α hd inverse ![r, q, s, productOuterTime inverse e] =
      chartOuterSurface P u v w α hd e ![r, q, s] := by
  exact BassMWholeNerve.chart_pause_outer_face P u v w α hd inverse e r q s

/-- One distinct fixed physical-factor face, with inverse time explicit. -/
theorem client_chart_pause_outer_face_0
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (r q s : unitInterval) :
    chartPause P u v w α hd inverse ![r, q, s, productOuterTime inverse 0] =
      chartOuterSurface P u v w α hd 0 ![r, q, s] := by
  exact BassMWholeNerve.chart_pause_outer_face P u v w α hd inverse 0 r q s

/-- One distinct fixed physical-factor face, with inverse time explicit. -/
theorem client_chart_pause_outer_face_1
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (r q s : unitInterval) :
    chartPause P u v w α hd inverse ![r, q, s, productOuterTime inverse 1] =
      chartOuterSurface P u v w α hd 1 ![r, q, s] := by
  exact BassMWholeNerve.chart_pause_outer_face P u v w α hd inverse 1 r q s

/-- Exact named whole-map consumer. -/
theorem client_polynomial_outer_zero
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (e : Fin 2) (q t : unitInterval) :
    polynomialOuterSurface P u v w α hc e ![0, q, productPolynomialTime inverse t] =
      polynomialProductPrism P u v w α hc inverse ![q, productEndpointTime e, t] := by
  exact BassMWholeNerve.polynomial_outer_zero P u v w α hc inverse e q t

/-- Exact named whole-map consumer. -/
theorem client_chart_outer_zero
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (e : Fin 2) (q s : unitInterval) :
    chartOuterSurface P u v w α hd e ![0, q, s] =
      chartProductPrism P u v w α hd inverse ![q, s, productOuterTime inverse e] := by
  exact BassMWholeNerve.chart_outer_zero P u v w α hd inverse e q s

/-- Exact named whole-map consumer. -/
theorem client_chart_outer_source
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (e : Fin 2) (r q : unitInterval) :
    chartOuterSurface P u v w α hd e ![r, q, 1] =
      chartProductPrism P u v w α hd inverse
        ![ChangedBoundaryPause.time (r, q), 1, productOuterTime inverse e] := by
  exact BassMWholeNerve.chart_outer_source P u v w α hd inverse e r q

/-- Exact named whole-map consumer. -/
theorem client_polynomial_outer_plus_coefficient_edge (e : Fin 2) (r q : unitInterval) :
    polynomialOuterSurface P u v w (underToLaurent R) (laurentPlus_projection P c) e ![r, q, 1] =
      coefficientPrismPause P u v w ![r, q, productEndpointTime e, 0] := by
  exact BassMWholeNerve.polynomial_outer_plus_coefficient_edge P u v w e r q

/-- Exact named whole-map consumer. -/
theorem client_polynomial_outer_minus_coefficient_edge (e : Fin 2) (r q : unitInterval) :
    polynomialOuterSurface P u v w (underToLaurentInvert R) (laurentMinus_projection P c) e
      ![r, q, 1] =
      coefficientPrismPause P u v w ![r, q, productEndpointTime e, 1] := by
  exact BassMWholeNerve.polynomial_outer_minus_coefficient_edge P u v w e r q

/-- Exact named whole-map consumer. -/
theorem client_chart_outer_plus_laurent_edge (e : Fin 2) (r q : unitInterval) :
    chartOuterSurface P u v w (underToLaurent R) (laurentPlus_projection P d) e ![r, q, 0] =
      laurentPrism P u v w ![q, 1, lower (productOuterTime false e)] := by
  exact BassMWholeNerve.chart_outer_plus_laurent_edge P u v w e r q

/-- Exact named whole-map consumer. -/
theorem client_chart_outer_minus_laurent_edge (e : Fin 2) (r q : unitInterval) :
    chartOuterSurface P u v w (underToLaurentInvert R) (laurentMinus_projection P d) e ![r, q, 0] =
      laurentPrism P u v w ![q, 1, upper (upper (productOuterTime true e))] := by
  exact BassMWholeNerve.chart_outer_minus_laurent_edge P u v w e r q

/-- Exact named whole-map consumer. -/
theorem client_polynomial_outer_boundary
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (e : Fin 2) (x : Quillen.SimplexCubeExtension.boundary) :
    polynomialOuterSurface P u v w α hc e x.val =
      CommonReferenceNerve.parameter _ (polynomialOuterNodes P u v w α hc e)
        (ChangedBoundaryPause.boundaryMap
          DoubleSquareScalarPaths.coefficientBoundaryParameter x) := by
  exact BassMWholeNerve.polynomial_outer_boundary P u v w α hc e x

/-- Exact named whole-map consumer. -/
theorem client_chart_outer_boundary
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (e : Fin 2) (x : Quillen.SimplexCubeExtension.boundary) :
    chartOuterSurface P u v w α hd e x.val =
      CommonReferenceNerve.parameter _ (chartOuterNodes P u v w α hd e)
        (ChangedBoundaryPause.boundaryMap
          DoubleSquareScalarPaths.coefficientBoundaryParameter x) := by
  exact BassMWholeNerve.chart_outer_boundary P u v w α hd e x

/-- Exact named whole-map consumer. -/
theorem client_polynomial_pause_coefficient_endpoint
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (e : Fin 2) (r s t : unitInterval) :
    polynomialPause P u v w α hc inverse ![r, productEndpointTime e, s, t] =
      polynomialProductPrism P u v w α hc inverse ![productEndpointTime e, s, t] := by
  exact BassMWholeNerve.polynomial_pause_coefficient_endpoint P u v w α hc inverse e r s t

/-- Exact named whole-map consumer. -/
theorem client_chart_pause_coefficient_endpoint
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (e : Fin 2) (r s t : unitInterval) :
    chartPause P u v w α hd inverse ![r, productEndpointTime e, s, t] =
      chartProductPrism P u v w α hd inverse ![productEndpointTime e, s, t] := by
  exact BassMWholeNerve.chart_pause_coefficient_endpoint P u v w α hd inverse e r s t

/-- Exact named whole-map consumer. -/
theorem client_polynomial_pause_plus_old_source (r s t : unitInterval) :
    polynomialPause P u v w (underToLaurent R) (laurentPlus_projection P c)
      false ![r, 0, s, t] =
      cubeLift P (u ≫ v) w (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (h0Anchor P (u ≫ v) w) ![1, upper s, lower t] := by
  exact BassMWholeNerve.polynomial_pause_plus_old_source P u v w r s t

/-- Exact named whole-map consumer. -/
theorem client_polynomial_pause_minus_old_source (r s t : unitInterval) :
    polynomialPause P u v w (underToLaurentInvert R) (laurentMinus_projection P c)
      true ![r, 0, s, t] =
      cubeLift P (u ≫ v) w (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (h0Anchor P (u ≫ v) w) ![1, upper s, upper (upper t)] := by
  exact BassMWholeNerve.polynomial_pause_minus_old_source P u v w r s t

/-- Exact named whole-map consumer. -/
theorem client_chart_pause_plus_old_source (r s t : unitInterval) :
    chartPause P u v w (underToLaurent R) (laurentPlus_projection P d)
      false ![r, 0, s, t] =
      cubeLift P u (v ≫ w) (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (rightStartingAnchor P u v w) ![1, upper s, lower t] := by
  exact BassMWholeNerve.chart_pause_plus_old_source P u v w r s t

/-- Exact named whole-map consumer. -/
theorem client_chart_pause_minus_old_source (r s t : unitInterval) :
    chartPause P u v w (underToLaurentInvert R) (laurentMinus_projection P d)
      true ![r, 0, s, t] =
      cubeLift P u (v ≫ w) (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (rightStartingAnchor P u v w) ![1, upper s, upper (upper t)] := by
  exact BassMWholeNerve.chart_pause_minus_old_source P u v w r s t

/-- Exact named whole-map consumer. -/
theorem client_polynomial_pause_plus_old_target (r s t : unitInterval) :
    polynomialPause P u v w (underToLaurent R) (laurentPlus_projection P c)
      false ![r, 1, s, upper t] =
      precompLift P u v w ![1, upper s, lower t] := by
  exact BassMWholeNerve.polynomial_pause_plus_old_target P u v w r s t

/-- Exact named whole-map consumer. -/
theorem client_polynomial_pause_minus_old_target (r s t : unitInterval) :
    polynomialPause P u v w (underToLaurentInvert R) (laurentMinus_projection P c)
      true ![r, 1, s, lower t] =
      precompLift P u v w ![1, upper s, upper (upper t)] := by
  exact BassMWholeNerve.polynomial_pause_minus_old_target P u v w r s t

/-- Exact named whole-map consumer. -/
theorem client_chart_pause_plus_old_target (r s t : unitInterval) :
    chartPause P u v w (underToLaurent R) (laurentPlus_projection P d)
      false ![r, 1, lower s, t] =
      postcompLift P u v w ![1, upper s, lower t] := by
  exact BassMWholeNerve.chart_pause_plus_old_target P u v w r s t

/-- Exact named whole-map consumer. -/
theorem client_chart_pause_minus_old_target (r s t : unitInterval) :
    chartPause P u v w (underToLaurentInvert R) (laurentMinus_projection P d)
      true ![r, 1, lower s, t] =
      postcompLift P u v w ![1, upper s, upper (upper t)] := by
  exact BassMWholeNerve.chart_pause_minus_old_target P u v w r s t

/-- Exact named whole-map consumer. -/
theorem client_product_pause_plus_middle (r s t : unitInterval) :
    polynomialPause P u v w (underToLaurent R) (laurentPlus_projection P c)
      false ![r, 1, s, lower t] =
    chartPause P u v w (underToLaurent R) (laurentPlus_projection P d)
      false ![r, 1, upper s, t] := by
  exact BassMWholeNerve.product_pause_plus_middle P u v w r s t

/-- Exact named whole-map consumer. -/
theorem client_product_pause_minus_middle (r s t : unitInterval) :
    polynomialPause P u v w (underToLaurentInvert R) (laurentMinus_projection P c)
      true ![r, 1, s, upper t] =
    chartPause P u v w (underToLaurentInvert R) (laurentMinus_projection P d)
      true ![r, 1, upper s, t] := by
  exact BassMWholeNerve.product_pause_minus_middle P u v w r s t

end Quillen.PerfectComplexes.BassMWholeNerve.OuterFaceClients
