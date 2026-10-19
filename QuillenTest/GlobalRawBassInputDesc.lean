/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputRawChartRows

/-! Regression checks for the complete original global raw input descent surface. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.GlobalRawBassInputDesc
open GlobalBassEvaluation GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Both full mixed geometric normalization intermediates are genuinely shared. -/
theorem target_outer_intermediate :
    InputChartReference.rawNode g plus GlobalRawBass.plus_projection 14 =
      InputChartReference.rawNode g minus GlobalRawBass.minus_projection 14 :=
  GlobalRawBass.InputDescNodes.plus_minus_target_intermediate_node g

/-- The entire inverse characteristic face retains its specified raw mixed nodes. -/
theorem inverse_characteristic (z : StdSimplex ℝ (Fin 18)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (GlobalRawBass.InputDescSimplex.mixedNodes g)
      (StdSimplex.map BassH0Diagram.minusFace.toOrderHom z) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputChartReference.rawNode g minus GlobalRawBass.minus_projection) z :=
  InputRawDesc.minus_characteristic g z

/-- The original geometric descent retains every point of its actual collapsed square. -/
theorem original_square (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (GlobalRawBass.InputDescSimplex.simplex g) n
      (BassH0Diagram.parameter (r, s), x) =
      (GlobalRawBass.inputDescPasting g).toSquare.level n (r, (s, x)) :=
  GlobalRawBass.InputDescSimplex.square_native g n r s x

/-- The whole continuous mixed surface is the original raw descent under actual evaluation. -/
theorem evaluated_whole (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (InputRawDesc.parameter g) n =
      (((GlobalRawBass.inputDescPasting g).toSquare.level n).comp
        (InputRawDesc.rawInputParameter (Y := Y) n)).comp
          (InputRawDesc.evaluationInputParameter (Y := Y) n) :=
  InputRawDesc.whole_native g n

/-- The original inverse raw-square row matches before any native evaluation. -/
theorem inverse_chart_row (z : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (GlobalRawBass.InputDescSimplex.mixedNodes g)
      (StdSimplex.map (InputRawChartRows.rowFace ≫ BassH0Diagram.minusFace).toOrderHom z) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (fun i => InputRawChartRows.projectedNode g minus GlobalRawBass.minus_projection
        (InputRawChartRows.squareNodes g minus i)) z :=
  InputRawChartRows.minus_parameter g z

/-- The entire positive edge retains the actual raw-square half clock in the mixed nerve. -/
theorem positive_chart_edge (t : unitInterval) :
    InputRawDesc.parameter g (t, 0) =
      CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
        (fun i => InputRawChartRows.projectedNode g plus GlobalRawBass.plus_projection
          (InputRawChartRows.squareNodes g plus i)) (NativeSquareFiveSimplex.parameter t) :=
  InputRawChartRows.left_parameter g t

end QuillenTest.GlobalRawBassInputDesc
