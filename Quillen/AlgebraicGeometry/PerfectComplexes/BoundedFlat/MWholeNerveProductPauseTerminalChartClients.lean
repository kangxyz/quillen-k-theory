/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPauseTerminalChart

/-!
# Terminal chart outer face against the literal source-whiskered old cube

Only the terminal paused square is transferred through the three original rectangle supports.
The full reference equality includes the original polynomial endpoint sourceIso and total.
The varying three-surface is not transferred into the old 140-node family.
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
namespace Quillen.PerfectComplexes.BassMWholeNerve.TerminalChartClients
open BassReferenceMerge BassH0Merge BassH1Join

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- Strict consumer of the full original statement. -/
theorem client_chart_terminal_anchor
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d) :
    chartFixedSideAnchor P u v w α hd 1 =
      precompAnchor P u v w ≪≫ isoWhiskerLeft (coefficientModel P u).functor
        (BassOverlap.commonToChartReference P v w α hd) := by
  exact BassMWholeNerve.chart_terminal_anchor P u v w α hd

/-- Strict consumer of the full original statement. -/
theorem client_chart_terminal_reference_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (i : Fin 18) :
    chartOuterNodes P u v w α hd 1 i =
      anchorNode (precompAnchor P u v w)
        (CommonReferenceNerve.precompNode (coefficientModel P u)
          (BassOverlap.chartOverlapNodes P v w α hd i)) := by
  exact BassMWholeNerve.chart_terminal_reference_nodes P u v w α hd i

/-- Strict consumer of the full original statement. -/
theorem client_terminal_old_plus_nodes (i : Fin 18) :
    precompNodes P u v w (terminalOldChartIndex false i) =
      chartOuterNodes P u v w (underToLaurent R) (laurentPlus_projection P d) 1 i := by
  exact BassMWholeNerve.terminal_old_plus_nodes P u v w i

/-- Strict consumer of the full original statement. -/
theorem client_terminal_old_minus_nodes (i : Fin 18) :
    precompNodes P u v w (terminalOldChartIndex true i) =
      chartOuterNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P d) 1 i := by
  exact BassMWholeNerve.terminal_old_minus_nodes P u v w i

/-- Strict consumer of the full original statement. -/
theorem client_chart_outer_terminal_plus (q s : unitInterval) :
    chartOuterSurface P u v w (underToLaurent R) (laurentPlus_projection P d) 1 ![1, q, s] =
      precompLift P u v w ![q, s, 0] := by
  exact BassMWholeNerve.chart_outer_terminal_plus P u v w q s

/-- Strict consumer of the full original statement. -/
theorem client_chart_outer_terminal_minus (q s : unitInterval) :
    chartOuterSurface P u v w (underToLaurentInvert R) (laurentMinus_projection P d) 1 ![1, q, s] =
      precompLift P u v w ![q, s, 1] := by
  exact BassMWholeNerve.chart_outer_terminal_minus P u v w q s

/-- The physical original ninety-node endpoint keeps every original coordinate. -/
theorem client_chart_pause_terminal_plus (q s : unitInterval) :
    chartPause P u v w (underToLaurent R) (laurentPlus_projection P d) false ![1, q, s, 1] =
      precompLift P u v w ![q, s, 0] := by
  have h := chart_pause_outer_face P u v w (underToLaurent R)
    (laurentPlus_projection P d) false 1 1 q s
  simpa [productOuterTime, productEndpointTime, productPolynomialTime] using
      h.trans (chart_outer_terminal_plus P u v w q s)

/-- The physical original ninety-node endpoint keeps every original coordinate. -/
theorem client_chart_pause_terminal_minus (q s : unitInterval) :
    chartPause P u v w (underToLaurentInvert R) (laurentMinus_projection P d) true ![1, q, s, 0] =
      precompLift P u v w ![q, s, 1] := by
  have h := chart_pause_outer_face P u v w (underToLaurentInvert R)
    (laurentMinus_projection P d) true 1 1 q s
  simpa [productOuterTime, productEndpointTime, productPolynomialTime] using
      h.trans (chart_outer_terminal_minus P u v w q s)

end Quillen.PerfectComplexes.BassMWholeNerve.TerminalChartClients
