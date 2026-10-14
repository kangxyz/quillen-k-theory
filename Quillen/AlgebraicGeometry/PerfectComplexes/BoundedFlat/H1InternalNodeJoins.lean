/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1ProductChartRows

/-! All original full reference nodes on the five internal H1 cell joins. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1Join

/-- Ordered along the original two binary paths; no monotone face assertion is made. -/
def polynomialWordIndex : Fin 5 → Fin 18 := ![5, 6, 13, 7, 17]

def chartWordIndex : Fin 5 → Fin 18 := ![9, 10, 11, 12, 13]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Every full polynomial-path node agrees with the actual product column. -/
theorem first_product_polynomial_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
    (i : Fin 5) :
    postReferenceNode (BassOverlap.commonReference P u v) (BassH1Components.laurentMap P v)
      (BassH1References.firstIso P u v)
      (BassH0Diagram.chartNodes P u α ha (polynomialWordIndex i)) =
      BassH1References.chartNodes P u v α hb (Quillen.SimplexGrid.index 4 4 (i, 2)) := by
  fin_cases i
  · exact first_product_polynomial_first_nodes P u v α ha hb 0
  · exact first_product_polynomial_first_nodes P u v α ha hb 1
  · exact first_product_polynomial_first_nodes P u v α ha hb 2
  · exact first_product_polynomial_second_nodes P u v α ha hb 1
  · exact first_product_polynomial_second_nodes P u v α ha hb 2

/-- Every full chart-path node agrees with the actual product row. -/
theorem middle_product_chart_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
    (i : Fin 5) :
    BassH0Merge.preReferenceNode (BassOverlap.commonReference P u v)
      (BassH1Components.coefficientMapModel P u) (BassH1References.middleIso P u v)
      (BassH0Diagram.chartNodes P v α hb (chartWordIndex i)) =
      BassH1References.chartNodes P u v α hb (Quillen.SimplexGrid.index 4 4 (4, i)) := by
  fin_cases i
  · exact middle_product_chart_first_nodes P u v α hb 0
  · exact middle_product_chart_first_nodes P u v α hb 1
  · exact middle_product_chart_first_nodes P u v α hb 2
  · exact middle_product_chart_second_nodes P u v α hb 1
  · exact middle_product_chart_second_nodes P u v α hb 2

/-- The complete positive first/product seam retains all five original dependent nodes. -/
theorem plus_column_nodes (i : Fin 5) :
    BassH1References.firstNodes P u v
      (BassH0Diagram.plusFace.toOrderHom (polynomialWordIndex i)) =
    BassH1References.chartNodes P u v (underToLaurent R) (laurentPlus_projection P b)
      (Quillen.SimplexGrid.index 4 4 (i, 2)) := by
  exact (congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.laurentMap P v) (BassH1References.firstIso P u v))
    (BassH0Diagram.plus_nodes P u (polynomialWordIndex i))).trans
    (first_product_polynomial_nodes P u v (underToLaurent R)
      (laurentPlus_projection P a) (laurentPlus_projection P b) i)

/-- The distinct inverse first/product seam retains its actual inverse-chart references. -/
theorem minus_column_nodes (i : Fin 5) :
    BassH1References.firstNodes P u v
      (BassH0Diagram.minusFace.toOrderHom (polynomialWordIndex i)) =
    BassH1References.chartNodes P u v (underToLaurentInvert R) (laurentMinus_projection P b)
      (Quillen.SimplexGrid.index 4 4 (i, 2)) := by
  exact (congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.laurentMap P v) (BassH1References.firstIso P u v))
    (BassH0Diagram.minus_nodes P u (polynomialWordIndex i))).trans
    (first_product_polynomial_nodes P u v (underToLaurentInvert R)
      (laurentMinus_projection P a) (laurentMinus_projection P b) i)

/-- All five original positive product/middle seam nodes share their entire references. -/
theorem plus_row_nodes (i : Fin 5) :
    BassH1References.middleNodes P u v
      (BassH0Diagram.plusFace.toOrderHom (chartWordIndex i)) =
    BassH1References.chartNodes P u v (underToLaurent R) (laurentPlus_projection P b)
      (Quillen.SimplexGrid.index 4 4 (4, i)) := by
  exact (congrArg (BassH0Merge.preReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.coefficientMapModel P u) (BassH1References.middleIso P u v))
    (BassH0Diagram.plus_nodes P v (chartWordIndex i))).trans
    (middle_product_chart_nodes P u v (underToLaurent R) (laurentPlus_projection P b) i)

/-- The same full-node assertion for the separate original inverse product/middle seam. -/
theorem minus_row_nodes (i : Fin 5) :
    BassH1References.middleNodes P u v
      (BassH0Diagram.minusFace.toOrderHom (chartWordIndex i)) =
    BassH1References.chartNodes P u v (underToLaurentInvert R) (laurentMinus_projection P b)
      (Quillen.SimplexGrid.index 4 4 (4, i)) := by
  exact (congrArg (BassH0Merge.preReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.coefficientMapModel P u) (BassH1References.middleIso P u v))
    (BassH0Diagram.minus_nodes P v (chartWordIndex i))).trans
    (middle_product_chart_nodes P u v (underToLaurentInvert R) (laurentMinus_projection P b) i)

end Quillen.PerfectComplexes.BassH1Join
