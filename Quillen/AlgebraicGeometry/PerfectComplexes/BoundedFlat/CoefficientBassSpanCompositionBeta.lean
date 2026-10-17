/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSpanCompositionLift
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSpanCompositionVertexBeta
public import Quillen.Aglib.Topology.Path.SpanReassociationNaturality

/-! The exact whole scalar seam between the original span composition and frozen M cube. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSpanCompositionReference
open CommonReferenceNerve BassMReassociation
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
local notation "E" => coefficientReference P p q
local notation "J" => polynomialMap P (c := c)

/-- The exact terminal first-stage row supplies every unchanged reassociation leaf. -/
theorem treeReassociation_beta (r s : I) :
    SSet.toTop.map (BassProjectionPath.WholeReference.FourEdge.beta P c E)
        (treeReassociation P p q (r, s)) =
      BassMWholeConeCarrier.parameter P p q
        (StdSimplex.map BassMWholeOrder.oldIndex (BassMReassociation.reassociation (r, s))) := by
  let f := (SSet.toTop.map (BassProjectionPath.WholeReference.FourEdge.beta P c E)).hom
  let g := (BassMWholeConeCarrier.parameter P p q).comp
    ⟨fun z : StdSimplex ℝ (Fin 131) ↦ StdSimplex.map BassMWholeOrder.oldIndex z,
      by fun_prop⟩
  let pL := (terminalFirstPath P p q).map
    (SSet.toTop.map (FourEdgeTree.plusVertex E J)).hom.continuous
  let qL := (terminalSecondAttached P p q).map
    (SSet.toTop.map (FourEdgeTree.plusVertex E J)).hom.continuous
  let tL := FourEdgeTree.overlapPath E J (coefficientPath P p q 1)
  let qR := (terminalSecondAttached P p q).symm.map
    (SSet.toTop.map (FourEdgeTree.minusVertex E J)).hom.continuous
  let pR := (terminalFirstPath P p q).symm.map
    (SSet.toTop.map (FourEdgeTree.minusVertex E J)).hom.continuous
  have htree (t : I) : treeSquare P p q (1, t) = treeReassociation P p q (1, t) :=
    FourEdgeTree.spanComposition_join E J (coefficientPath P p q 1)
      (terminalFirstPath P p q) (terminalSecondAttached P p q)
      (polynomialSquare P p q) (coefficientPath P p q) (polynomialSquare_attachment P p q)
      rfl (polynomialSquare_terminal P p q) t
  have hm (t : I) : BassMScalarPasting.vertex.{u} BassMWholeOrder.vertexIndex (1, t) =
      StdSimplex.map BassMWholeOrder.oldIndex
        (((Ppath.trans Qpath).trans (Tpath.trans (Upath.trans Vpath))) t) := by
    have h := BassMScalarPasting.stage_join BassMWholeOrder.vertexIndex
      BassMWholeOrder.oldIndex BassMWhole.indexEqualities t
    change BassMScalarPasting.vertex.{u} BassMWholeOrder.vertexIndex (1, t) =
      StdSimplex.map BassMWholeOrder.oldIndex (secondParameter (0, t)) at h
    exact h.trans (congrArg (StdSimplex.map BassMWholeOrder.oldIndex) (second_zero t))
  have htarget (t : I) :
      f (((pL.trans qL).trans (tL.trans (qR.trans pR))) t) =
        g (((Ppath.trans Qpath).trans (Tpath.trans (Upath.trans Vpath))) t) := by
    calc
      _ = f (treeReassociation P p q (1, t)) :=
        congrArg f ((treeReassociation P p q).apply_one t).symm
      _ = f (treeSquare P p q (1, t)) := congrArg f (htree t).symm
      _ = BassMWholeConeCarrier.parameter P p q
          (BassMScalarPasting.vertex.{u} BassMWholeOrder.vertexIndex (1, t)) :=
        treeSquare_beta P p q 1 t
      _ = _ := congrArg (BassMWholeConeCarrier.parameter P p q) (hm t)
  exact Path.Evaluation.spanReassociation_of_target f g pL qL tL qR pR
    Ppath Qpath Tpath Upath Vpath htarget r s

/-- The original whole A and original M top are the same full Laurent-carrier value. -/
theorem treeComposition_beta (r t : I) :
    SSet.toTop.map (BassProjectionPath.WholeReference.FourEdge.beta P c E)
        (treeComposition P p q (r, t)) =
      BassMWholeConeCarrier.parameter P p q (BassMWhole.mParameter.{u} (r, t)) := by
  rcases cover r with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [treeComposition_lower, BassMWhole.mParameter, BassMScalarPasting.parameter_lower]
    exact treeSquare_beta P p q s t
  · rw [treeComposition_upper, BassMWhole.mParameter, BassMScalarPasting.parameter_upper]
    exact treeReassociation_beta P p q (unitInterval.symm s) t

end Quillen.PerfectComplexes.CoefficientBassSpanCompositionReference
