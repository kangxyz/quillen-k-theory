/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.ChangedBoundaryPauseCube
public import Quillen.Waldhausen.SConstruction.Iterated.ChangedBoundaryPauseTime
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPrismSides

/-!
# The actual product pause comparisons and the changing coefficient prism

The interior exists only in the scalar eighteen-node simplex. Every resulting nerve map
uses the original ninety-node family and its original anchor. The coefficient prism changes
by the exact transRefl time; no arbitrary nerve-valued extension is invoked.
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

/-- The pause-comparison time precedes the three unchanged original prism coordinates. -/
abbrev PauseCube := Fin 4 → unitInterval

/-- Specialize the constructed scalar cube to the actual original coefficient boundary word. -/
def coefficientPauseCube : C(Quillen.SimplexCubeExtension.Cube, StdSimplex ℝ (Fin 18)) :=
  ChangedBoundaryPause.cube DoubleSquareScalarPaths.coefficientBoundaryParameter

/-- Keep both independent product factors and the exact inverse-polynomial coordinate. -/
def polynomialPauseParameter (inverse : Bool) : C(PauseCube, StdSimplex ℝ (Fin 90)) :=
  ⟨fun z ↦ Quillen.SimplexGrid.parameter.{u + 1} 17 4
    (coefficientPauseCube ![z 0, z 1, productPolynomialTime inverse (z 3)],
      NativeSquareFiveSimplex.parameter (z 2)), by fun_prop⟩

/-- Only the moving-chart factor receives the changed-boundary scalar cube. -/
def chartPauseParameter (inverse : Bool) : C(PauseCube, StdSimplex ℝ (Fin 90)) :=
  ⟨fun z ↦ Quillen.SimplexGrid.parameter.{u + 1} 4 17
    (NativeSquareFiveSimplex.parameter (productPolynomialTime inverse (z 3)),
      coefficientPauseCube ![z 0, z 1, z 2]), by fun_prop⟩

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- The same ninety complete polynomial-product nodes and their specified reference iso. -/
def polynomialPause
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) : C(PauseCube, |nerve (Codiscrete (CommonReferenceNerve.Node
      (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|) :=
  (CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w α hc)).comp
    (polynomialPauseParameter.{u} inverse)

/-- The chart product retains its distinct original factorization and anchor. -/
def chartPause
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) : C(PauseCube, |nerve (Codiscrete (CommonReferenceNerve.Node
      (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|) :=
  (CommonReferenceNerve.parameter _ (chartProductNodes P u v w α hd)).comp
    (chartPauseParameter.{u} inverse)

/-- The changing coefficient comparison is explicitly constructed from the actual Pc map. -/
def coefficientPrismPause : C(PauseCube, |nerve (Codiscrete (CommonReferenceNerve.Node
      (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|) :=
  ⟨fun z ↦ coefficientPrism P u v w
    ![ChangedBoundaryPause.time (z 0, z 1), z 2, z 3], by fun_prop⟩

/-- Every original polynomial prism point is the actual initial pause-comparison face. -/
theorem polynomial_pause_zero
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (q s t : unitInterval) :
    polynomialPause P u v w α hc inverse ![0, q, s, t] =
      polynomialProductPrism P u v w α hc inverse ![q, s, t] := by
  change CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w α hc)
    (Quillen.SimplexGrid.parameter.{u + 1} 17 4
      (ChangedBoundaryPause.cube DoubleSquareScalarPaths.coefficientBoundaryParameter
        ![0, q, productPolynomialTime inverse t], NativeSquareFiveSimplex.parameter s)) = _
  rw [ChangedBoundaryPause.cube_zero]
  rfl

/-- Every original chart prism point, including its independent inverse time, is retained. -/
theorem chart_pause_zero
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (q s t : unitInterval) :
    chartPause P u v w α hd inverse ![0, q, s, t] =
      chartProductPrism P u v w α hd inverse ![q, s, t] := by
  change CommonReferenceNerve.parameter _ (chartProductNodes P u v w α hd)
    (Quillen.SimplexGrid.parameter.{u + 1} 4 17
      (NativeSquareFiveSimplex.parameter (productPolynomialTime inverse t),
        ChangedBoundaryPause.cube DoubleSquareScalarPaths.coefficientBoundaryParameter
          ![0, q, s])) = _
  rw [ChangedBoundaryPause.cube_zero]
  rfl

/-- Pc starts at its unchanged actual whole map, not merely a canonically isomorphic map. -/
theorem coefficient_prism_pause_zero (q s t : unitInterval) :
    coefficientPrismPause P u v w ![0, q, s, t] = coefficientPrism P u v w ![q, s, t] := by
  change coefficientPrism P u v w ![ChangedBoundaryPause.time (0, q), s, t] = _
  rw [ChangedBoundaryPause.time_zero]

/-- The changing polynomial source side is exactly the original raw side at transRefl time. -/
theorem polynomial_pause_source_side
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (a q s t : unitInterval)
    (ht : productPolynomialTime inverse t = 1) :
    polynomialPause P u v w α hc inverse ![a, q, s, t] =
      polynomialProductPrism P u v w α hc inverse
        ![ChangedBoundaryPause.time (a, q), s, t] := by
  change CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w α hc)
    (Quillen.SimplexGrid.parameter.{u + 1} 17 4
      (ChangedBoundaryPause.cube DoubleSquareScalarPaths.coefficientBoundaryParameter
        ![a, q, productPolynomialTime inverse t], NativeSquareFiveSimplex.parameter s)) =
    CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w α hc)
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter
          (ChangedBoundaryPause.time (a, q), productPolynomialTime inverse t),
          NativeSquareFiveSimplex.parameter s))
  rw [ht, ChangedBoundaryPause.cube_right, ChangedBoundaryPause.rightEdge_apply,
    CoefficientMovingSquareRows.moving_right]

/-- The Pl-facing chart side remains the entire old side, not only its endpoints. -/
theorem chart_pause_target_side
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (a q t : unitInterval) :
    chartPause P u v w α hd inverse ![a, q, 0, t] =
      chartProductPrism P u v w α hd inverse ![q, 0, t] := by
  change CommonReferenceNerve.parameter _ (chartProductNodes P u v w α hd)
    (Quillen.SimplexGrid.parameter.{u + 1} 4 17
      (NativeSquareFiveSimplex.parameter (productPolynomialTime inverse t),
        ChangedBoundaryPause.cube DoubleSquareScalarPaths.coefficientBoundaryParameter
          ![a, q, 0])) =
    CommonReferenceNerve.parameter _ (chartProductNodes P u v w α hd)
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (NativeSquareFiveSimplex.parameter (productPolynomialTime inverse t),
          DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, 0)))
  rw [ChangedBoundaryPause.cube_left, CoefficientMovingSquareRows.moving_left]

/-- The complete Pc scalar side, with the actual five-node chart order in its H0 factor. -/
theorem coefficient_chart_side_parameter (inverse : Bool)
    (z : StdSimplex ℝ (Fin 3)) (s : unitInterval) :
    Quillen.SimplexGrid.parameter.{u + 1} 2 30
      (z, ProjectionRectangleParameters.L (productProjectionFace inverse) s) =
      StdSimplex.map (coefficientChartSideIndex (productProjectionFace inverse))
        (Quillen.SimplexGrid.parameter.{u + 1} 2 4
          (z, NativeSquareFiveSimplex.parameter s)) := by
  let β : ⦋4⦌ ⟶ ⦋30⦌ := SimplexCategory.Hom.mk
    ⟨(productProjectionFace inverse).toOrderHom ∘ ProjectionRectangleSquareRows.chartRow,
      (by decide : ∀ b : Bool, Monotone ((productProjectionFace b).toOrderHom ∘
        ProjectionRectangleSquareRows.chartRow)) inverse⟩
  let γ : ⦋14⦌ ⟶ ⦋92⦌ := SimplexCategory.Hom.mk
    ⟨coefficientChartSideIndex (productProjectionFace inverse),
      (by decide : ∀ b : Bool,
        Monotone (coefficientChartSideIndex (productProjectionFace b))) inverse⟩
  have hγ : ∀ i j, γ.toOrderHom (Quillen.SimplexGrid.index 2 4 (i, j)) =
      Quillen.SimplexGrid.index 2 30
        ((SimplexCategory.Hom.toOrderHom (𝟙 ⦋2⦌)) i, β.toOrderHom j) := by
    intro i j
    change coefficientChartSideIndex (productProjectionFace inverse)
      (Quillen.SimplexGrid.index 2 4 (i, j)) = _
    unfold coefficientChartSideIndex
    rw [Quillen.SimplexGrid.decode_index]
    rfl
  have h := Quillen.SimplexGrid.parameter_productMap.{u + 1}
    (𝟙 ⦋2⦌) β γ hγ z (NativeSquareFiveSimplex.parameter s)
  have hid : StdSimplex.map
      (SimplexCategory.Hom.toOrderHom (𝟙 ⦋2⦌) : Fin 3 → Fin 3) z = z := by
    change StdSimplex.map id z = z
    exact StdSimplex.map_id z
  exact (congrArg (Quillen.SimplexGrid.parameter.{u + 1} 2 30)
    (Prod.ext hid.symm
      (ProjectionRectangleSquareRows.chart_parameter
        (productProjectionFace inverse) s).symm)).trans h

/-- The whole actual Pc left face equals the same canonical characteristic map. -/
theorem coefficient_prism_left_side (q s : unitInterval) :
    coefficientPrism P u v w ![q, s, 0] =
      CommonReferenceNerve.parameter _ (coefficientPrismNodes P u v w)
        (StdSimplex.map (coefficientChartSideIndex BassH0Diagram.plusFace)
          (Quillen.SimplexGrid.parameter.{u + 1} 2 4
            (binaryPath (k := 2) 0 1 2 q, NativeSquareFiveSimplex.parameter s))) := by
  change CommonReferenceNerve.parameter _ (coefficientPrismNodes P u v w)
    (Quillen.SimplexGrid.parameter.{u + 1} 2 30
      (binaryPath (k := 2) 0 1 2 q, BassH0Diagram.parameter (s, 0))) = _
  rw [BassH0Diagram.parameter_left]
  exact congrArg (CommonReferenceNerve.parameter _ (coefficientPrismNodes P u v w))
    (coefficient_chart_side_parameter false _ s)

/-- The whole actual Pc right face retains the inverse chart and its original orientation. -/
theorem coefficient_prism_right_side (q s : unitInterval) :
    coefficientPrism P u v w ![q, s, 1] =
      CommonReferenceNerve.parameter _ (coefficientPrismNodes P u v w)
        (StdSimplex.map (coefficientChartSideIndex BassH0Diagram.minusFace)
          (Quillen.SimplexGrid.parameter.{u + 1} 2 4
            (binaryPath (k := 2) 0 1 2 q, NativeSquareFiveSimplex.parameter s))) := by
  change CommonReferenceNerve.parameter _ (coefficientPrismNodes P u v w)
    (Quillen.SimplexGrid.parameter.{u + 1} 2 30
      (binaryPath (k := 2) 0 1 2 q, BassH0Diagram.parameter (s, 1))) = _
  rw [BassH0Diagram.parameter_right]
  exact congrArg (CommonReferenceNerve.parameter _ (coefficientPrismNodes P u v w))
    (coefficient_chart_side_parameter true _ s)

/-- The changing plus Pc seam is genuinely matched as an actual whole nerve map. -/
theorem polynomial_pause_plus_coefficient_seam (a q s : unitInterval) :
    polynomialPause P u v w (underToLaurent R) (laurentPlus_projection P c) false
      ![a, q, s, 1] = coefficientPrismPause P u v w ![a, q, s, 0] := by
  rw [polynomial_pause_source_side P u v w _ _ false a q s 1 rfl,
    polynomial_plus_composition_side]
  exact (coefficient_prism_left_side P u v w (ChangedBoundaryPause.time (a, q)) s).symm

/-- The inverse polynomial endpoint is zero; comparison, coefficient and chart times stay put. -/
theorem polynomial_pause_minus_coefficient_seam (a q s : unitInterval) :
    polynomialPause P u v w (underToLaurentInvert R) (laurentMinus_projection P c) true
      ![a, q, s, 0] = coefficientPrismPause P u v w ![a, q, s, 1] := by
  rw [polynomial_pause_source_side P u v w _ _ true a q s 0
    (by simp [productPolynomialTime]), polynomial_minus_composition_side]
  exact (coefficient_prism_right_side P u v w (ChangedBoundaryPause.time (a, q)) s).symm

end Quillen.PerfectComplexes.BassMWholeNerve

