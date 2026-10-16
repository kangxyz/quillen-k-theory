/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveTerminalChartComparison

/-!
# The existing terminal chart comparison and all six actual faces

The lateral faces genuinely vary with comparison time. This is the original ninety-node
terminal product cube, not a new extension and not a homotopy relative to its lateral boundary.
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
namespace Quillen.PerfectComplexes.BassMWholeNerve.TerminalComparisonClients
open BassReferenceMerge BassH0Merge BassH1Join

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- Strict named whole-face consumer, retaining all independent coordinates. -/
theorem client_terminal_chart_comparison_zero
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (q s : unitInterval) :
    terminalChartComparison P u v w α hd inverse ![0, q, s] =
      chartOuterSurface P u v w α hd 0 ![1, q, s] := by
  exact BassMWholeNerve.terminal_chart_comparison_zero P u v w α hd inverse q s

/-- Strict named whole-face consumer, retaining all independent coordinates. -/
theorem client_terminal_chart_comparison_one
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (q s : unitInterval) :
    terminalChartComparison P u v w α hd inverse ![1, q, s] =
      chartOuterSurface P u v w α hd 1 ![1, q, s] := by
  exact BassMWholeNerve.terminal_chart_comparison_one P u v w α hd inverse q s

/-- Strict named whole-face consumer, retaining all independent coordinates. -/
theorem client_terminal_chart_comparison_plus_one (q s : unitInterval) :
    terminalChartComparison P u v w (underToLaurent R) (laurentPlus_projection P d)
      false ![1, q, s] = precompLift P u v w ![q, s, 0] := by
  exact BassMWholeNerve.terminal_chart_comparison_plus_one P u v w q s

/-- Strict named whole-face consumer, retaining all independent coordinates. -/
theorem client_terminal_chart_comparison_minus_one (q s : unitInterval) :
    terminalChartComparison P u v w (underToLaurentInvert R) (laurentMinus_projection P d)
      true ![1, q, s] = precompLift P u v w ![q, s, 1] := by
  exact BassMWholeNerve.terminal_chart_comparison_minus_one P u v w q s

/-- Strict named whole-face consumer, retaining all independent coordinates. -/
theorem client_terminal_chart_comparison_source
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (h s : unitInterval) :
    terminalChartComparison P u v w α hd inverse ![h, 0, s] =
      chartProductPrism P u v w α hd inverse
        ![0, s, productPolynomialTime inverse h] := by
  exact BassMWholeNerve.terminal_chart_comparison_source P u v w α hd inverse h s

/-- Strict named whole-face consumer, retaining all independent coordinates. -/
theorem client_terminal_chart_comparison_target
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (h s : unitInterval) :
    terminalChartComparison P u v w α hd inverse ![h, 1, s] =
      chartProductPrism P u v w α hd inverse
        ![1, s, productPolynomialTime inverse h] := by
  exact BassMWholeNerve.terminal_chart_comparison_target P u v w α hd inverse h s

/-- Strict named whole-face consumer, retaining all independent coordinates. -/
theorem client_terminal_chart_comparison_left
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (h q : unitInterval) :
    terminalChartComparison P u v w α hd inverse ![h, q, 0] =
      chartProductPrism P u v w α hd inverse
        ![q, 0, productPolynomialTime inverse h] := by
  exact BassMWholeNerve.terminal_chart_comparison_left P u v w α hd inverse h q

/-- Strict named whole-face consumer, retaining all independent coordinates. -/
theorem client_terminal_chart_comparison_right
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (h q : unitInterval) :
    terminalChartComparison P u v w α hd inverse ![h, q, 1] =
      chartProductPrism P u v w α hd inverse
        ![ChangedBoundaryPause.terminalTime q, 1, productPolynomialTime inverse h] := by
  exact BassMWholeNerve.terminal_chart_comparison_right P u v w α hd inverse h q

/-- Strict named whole-face consumer, retaining all independent coordinates. -/
theorem client_terminal_chart_comparison_plus_laurent (h q : unitInterval) :
    terminalChartComparison P u v w (underToLaurent R) (laurentPlus_projection P d)
      false ![h, q, 0] = laurentPrism P u v w ![q, 1, lower h] := by
  exact BassMWholeNerve.terminal_chart_comparison_plus_laurent P u v w h q

/-- Strict named whole-face consumer, retaining all independent coordinates. -/
theorem client_terminal_chart_comparison_minus_laurent (h q : unitInterval) :
    terminalChartComparison P u v w (underToLaurentInvert R) (laurentMinus_projection P d)
      true ![h, q, 0] = laurentPrism P u v w ![q, 1, upper (upper (unitInterval.symm h))] := by
  exact BassMWholeNerve.terminal_chart_comparison_minus_laurent P u v w h q

end Quillen.PerfectComplexes.BassMWholeNerve.TerminalComparisonClients
