/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1ProductOuterRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1OuterScalarWords

/-! Full original outer H1 edge nodes in the fixed H0/chart/bottom62 family. -/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1Join

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The first half of the outer edge retains every original functor and reference node. -/
theorem first_old_chart_word_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (i : Fin 5) :
    postReferenceNode (BassOverlap.commonReference P u v) (BassH1Components.laurentMap P v)
      (BassH1References.firstIso P u v) (BassH0Diagram.chartNodes P u α ha (chartWordIndex i)) =
    BassOverlap.chartOverlapNodes P u v α hc (outerFirstWordIndex i) := by
  fin_cases i
  · exact first_old_chart_center P u v α ha hc
  · exact first_old_outer_first_nodes P u v α ha hc 1
  · exact first_old_outer_first_nodes P u v α ha hc 2
  · exact first_old_outer_second_nodes P u v α ha hc 1
  · exact first_old_outer_second_nodes P u v α ha hc 2

/-- The other half uses the actual varying-family product row and its unchanged full references. -/
theorem product_old_chart_word_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (i : Fin 5) :
    BassH1References.chartNodes P u v α hb (Quillen.SimplexGrid.index 4 4 (2, i)) =
    BassOverlap.chartOverlapNodes P u v α hc (outerProductWordIndex i) := by
  fin_cases i
  · exact product_old_outer_first_nodes P u v α ha hb hc 0
  · exact product_old_outer_first_nodes P u v α ha hb hc 1
  · exact product_old_outer_first_nodes P u v α ha hb hc 2
  · exact product_old_outer_second_nodes P u v α ha hb hc 1
  · exact product_old_outer_second_nodes P u v α ha hb hc 2

/-- All five first-half positive nodes are the original fixed old62 nodes. -/
theorem first_old62_plus_nodes (i : Fin 5) :
    BassH1References.firstNodes P u v
      (BassH0Diagram.plusFace.toOrderHom (chartWordIndex i)) =
    BassH0Merged.nodes P u v (BassSupportOrder.oldIndex (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.plusFace.toOrderHom (outerFirstWordIndex i)))) := by
  exact (congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.laurentMap P v) (BassH1References.firstIso P u v))
    (BassH0Diagram.plus_nodes P u (chartWordIndex i))).trans
    ((first_old_chart_word_nodes P u v (underToLaurent R)
      (laurentPlus_projection P a) (laurentPlus_projection P c) i).trans
      ((BassH0Merge.old_plus_node P u v _).symm.trans (BassH0Merged.old_nodes P u v _).symm))

/-- All five first-half inverse nodes retain their separate inverse-coordinate references. -/
theorem first_old62_minus_nodes (i : Fin 5) :
    BassH1References.firstNodes P u v
      (BassH0Diagram.minusFace.toOrderHom (chartWordIndex i)) =
    BassH0Merged.nodes P u v (BassSupportOrder.oldIndex (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.minusFace.toOrderHom (outerFirstWordIndex i)))) := by
  exact (congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.laurentMap P v) (BassH1References.firstIso P u v))
    (BassH0Diagram.minus_nodes P u (chartWordIndex i))).trans
    ((first_old_chart_word_nodes P u v (underToLaurentInvert R)
      (laurentMinus_projection P a) (laurentMinus_projection P c) i).trans
      ((BassH0Merge.old_minus_node P u v _).symm.trans (BassH0Merged.old_nodes P u v _).symm))

/-- The whole positive product outer row agrees with the unchanged second half of the old chart. -/
theorem product_old62_plus_nodes (i : Fin 5) :
    BassH1References.chartNodes P u v (underToLaurent R) (laurentPlus_projection P b)
      (Quillen.SimplexGrid.index 4 4 (2, i)) =
    BassH0Merged.nodes P u v (BassSupportOrder.oldIndex (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.plusFace.toOrderHom (outerProductWordIndex i)))) :=
  (product_old_chart_word_nodes P u v (underToLaurent R) (laurentPlus_projection P a)
    (laurentPlus_projection P b) (laurentPlus_projection P c) i).trans
    ((BassH0Merge.old_plus_node P u v _).symm.trans (BassH0Merged.old_nodes P u v _).symm)

/-- The whole inverse product row retains its original second-half inverse chart references. -/
theorem product_old62_minus_nodes (i : Fin 5) :
    BassH1References.chartNodes P u v (underToLaurentInvert R) (laurentMinus_projection P b)
      (Quillen.SimplexGrid.index 4 4 (2, i)) =
    BassH0Merged.nodes P u v (BassSupportOrder.oldIndex (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.minusFace.toOrderHom (outerProductWordIndex i)))) :=
  (product_old_chart_word_nodes P u v (underToLaurentInvert R) (laurentMinus_projection P a)
    (laurentMinus_projection P b) (laurentMinus_projection P c) i).trans
    ((BassH0Merge.old_minus_node P u v _).symm.trans (BassH0Merged.old_nodes P u v _).symm)

end Quillen.PerfectComplexes.BassH1Join
