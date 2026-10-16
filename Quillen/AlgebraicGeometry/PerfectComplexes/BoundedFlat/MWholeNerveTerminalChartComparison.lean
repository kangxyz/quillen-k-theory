/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPauseTerminalChart

/-!
# The existing terminal chart comparison and all six actual faces

The lateral faces genuinely vary with comparison time. This is the original ninety-node
terminal product cube, not a new extension and not a homotopy relative to its lateral boundary.
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

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- The inverse orientation reverses only physical polynomial time, so both signs run e0 to e1. -/
def terminalChartComparison
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) : C(Quillen.SimplexCubeExtension.Cube,
      |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|) :=
  ⟨fun z ↦ chartPause P u v w α hd inverse
    ![1, z 1, z 2, productPolynomialTime inverse (z 0)], by fun_prop⟩

/-- Initial comparison face is the entire remaining terminal e0 surface. -/
theorem terminal_chart_comparison_zero
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (q s : unitInterval) :
    terminalChartComparison P u v w α hd inverse ![0, q, s] =
      chartOuterSurface P u v w α hd 0 ![1, q, s] := by
  exact chart_pause_outer_face P u v w α hd inverse 0 1 q s

/-- Final comparison face is the original e1 surface before its literal old-map identification. -/
theorem terminal_chart_comparison_one
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (q s : unitInterval) :
    terminalChartComparison P u v w α hd inverse ![1, q, s] =
      chartOuterSurface P u v w α hd 1 ![1, q, s] := by
  exact chart_pause_outer_face P u v w α hd inverse 1 1 q s

/-- The whole final plus face is the unchanged old precomp cube chart side. -/
theorem terminal_chart_comparison_plus_one (q s : unitInterval) :
    terminalChartComparison P u v w (underToLaurent R) (laurentPlus_projection P d)
      false ![1, q, s] = precompLift P u v w ![q, s, 0] := by
  rw [terminal_chart_comparison_one]
  exact chart_outer_terminal_plus P u v w q s

/-- The whole final minus face is the unchanged old precomp cube chart side. -/
theorem terminal_chart_comparison_minus_one (q s : unitInterval) :
    terminalChartComparison P u v w (underToLaurentInvert R) (laurentMinus_projection P d)
      true ![1, q, s] = precompLift P u v w ![q, s, 1] := by
  rw [terminal_chart_comparison_one]
  exact chart_outer_terminal_minus P u v w q s

/-- This whole q=0 lateral face retains its original ninety-node product map. -/
theorem terminal_chart_comparison_source
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (h s : unitInterval) :
    terminalChartComparison P u v w α hd inverse ![h, 0, s] =
      chartProductPrism P u v w α hd inverse
        ![0, s, productPolynomialTime inverse h] := by
  exact chart_pause_coefficient_endpoint P u v w α hd inverse 0 1 s _

/-- This whole q=1 lateral face retains its original ninety-node product map. -/
theorem terminal_chart_comparison_target
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (h s : unitInterval) :
    terminalChartComparison P u v w α hd inverse ![h, 1, s] =
      chartProductPrism P u v w α hd inverse
        ![1, s, productPolynomialTime inverse h] := by
  exact chart_pause_coefficient_endpoint P u v w α hd inverse 1 1 s _

/-- The s=0 lateral face is fixed in pause time, but varies in physical polynomial time. -/
theorem terminal_chart_comparison_left
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (h q : unitInterval) :
    terminalChartComparison P u v w α hd inverse ![h, q, 0] =
      chartProductPrism P u v w α hd inverse
        ![q, 0, productPolynomialTime inverse h] := by
  exact chart_pause_target_side P u v w α hd inverse 1 q _

/-- The s=1 lateral face retains the genuine terminal pause in the raw coefficient coordinate. -/
theorem terminal_chart_comparison_right
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (h q : unitInterval) :
    terminalChartComparison P u v w α hd inverse ![h, q, 1] =
      chartProductPrism P u v w α hd inverse
        ![ChangedBoundaryPause.terminalTime q, 1, productPolynomialTime inverse h] := by
  change chartPause P u v w α hd inverse ![1, q, 1, productPolynomialTime inverse h] = _
  rw [chart_pause_source_side, ChangedBoundaryPause.time_one]

/-- The actual varying Pl subface keeps its original plus subinterval coordinate. -/
theorem terminal_chart_comparison_plus_laurent (h q : unitInterval) :
    terminalChartComparison P u v w (underToLaurent R) (laurentPlus_projection P d)
      false ![h, q, 0] = laurentPrism P u v w ![q, 1, lower h] := by
  exact chart_pause_plus_laurent_seam P u v w 1 q _

/-- The actual varying Pl subface keeps its original minus subinterval coordinate. -/
theorem terminal_chart_comparison_minus_laurent (h q : unitInterval) :
    terminalChartComparison P u v w (underToLaurentInvert R) (laurentMinus_projection P d)
      true ![h, q, 0] = laurentPrism P u v w ![q, 1, upper (upper (unitInterval.symm h))] := by
  exact chart_pause_minus_laurent_seam P u v w 1 q _

end Quillen.PerfectComplexes.BassMWholeNerve
