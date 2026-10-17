/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetTerminalPolynomialRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0ChartBoundaryRows

/-! The original moving chart and target-oriented polynomial square meet at their full node. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTerminalChartJoin
open BassH0Merge BassH1Join CommonReferenceNerve
open BassProjectionPath.WholeReference.FourEdge.Target
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)

/-- The unchanged final chart node is the initial polynomial-square node in its terminal anchor. -/
theorem positive_node :
    BassH0ChartBoundaryRows.preNode P f (underToLaurent R) (laurentPlus_projection P a)
      (BassH0ChartBoundaryRows.squareNodes P f (underToLaurent R) 4) =
    postReferenceNode (BassH0Diagram.reference P f) (normalizedMap (laurentPlus P b))
      (terminalPolynomialAnchor P f (underToLaurent R) (laurentPlus_projection P b))
      (CoefficientSquareFamilies.polynomialNodes P f 2) := by
  have hc := BassH0ChartBoundaryRows.chart_nodes P f (underToLaurent R)
    (laurentPlus_projection P a) 4
  have hp := terminal_polynomial_plus_nodes P f 2
  exact hc.symm.trans hp

/-- The inverse chart retains its separate complete anchor at the same original square clock. -/
theorem negative_node :
    BassH0ChartBoundaryRows.preNode P f (underToLaurentInvert R) (laurentMinus_projection P a)
      (BassH0ChartBoundaryRows.squareNodes P f (underToLaurentInvert R) 4) =
    postReferenceNode (BassH0Diagram.reference P f) (normalizedMap (laurentMinus P b))
      (terminalPolynomialAnchor P f (underToLaurentInvert R) (laurentMinus_projection P b))
      (CoefficientSquareFamilies.polynomialNodes P f 2) := by
  have hc := BassH0ChartBoundaryRows.chart_nodes P f (underToLaurentInvert R)
    (laurentMinus_projection P a) 4
  have hp := terminal_polynomial_minus_nodes P f 2
  exact hc.symm.trans hp

/-- The positive shared node retains its full chart and polynomial normalization anchors. -/
theorem positive_anchor :
    BassH0ChartBoundaryRows.canonicalAnchor P f (underToLaurent R)
        (laurentPlus_projection P a) ≪≫
      isoWhiskerLeft (normalizedMap (polynomialProjection P a)).functor
        (BassH0ChartBoundaryRows.squareNodes P f (underToLaurent R) 4).2 =
    terminalPolynomialAnchor P f (underToLaurent R) (laurentPlus_projection P b) ≪≫
      isoWhiskerRight (CoefficientSquareFamilies.polynomialNodes P f 2).2
        (normalizedMap (laurentPlus P b)).functor := by
  exact eq_of_heq (Sigma.mk.inj (positive_node P f)).2

/-- The inverse chart has its own complete normalization equality, with no sign identification. -/
theorem negative_anchor :
    BassH0ChartBoundaryRows.canonicalAnchor P f (underToLaurentInvert R)
        (laurentMinus_projection P a) ≪≫
      isoWhiskerLeft (normalizedMap (polynomialProjection P a)).functor
        (BassH0ChartBoundaryRows.squareNodes P f (underToLaurentInvert R) 4).2 =
    terminalPolynomialAnchor P f (underToLaurentInvert R) (laurentMinus_projection P b) ≪≫
      isoWhiskerRight (CoefficientSquareFamilies.polynomialNodes P f 2).2
        (normalizedMap (laurentMinus P b)).functor := by
  exact eq_of_heq (Sigma.mk.inj (negative_node P f)).2

end Quillen.PerfectComplexes.CoefficientBassSeedTerminalChartJoin
