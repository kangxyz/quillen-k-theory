/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Realization.TwoSidedBar.ZeroFiber

/-! Semantic tests for the original zero-row chain, both augmentations,
complete stored paths, finite degree zero, and genuinely empty fibers. -/
@[expose] public section

noncomputable section
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Tests.TwoSidedBarZeroFiber
open Quillen Quillen.TheoremA Quillen.TwoSidedBar
variable {H J : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : H ⟶ J)
  (h : Quillen.CartesianRealization.Skeletal.TransitionWeakCartesian
    (Functor.whiskerLeft indexProjection η))

example : barZeroInclusion H ≫ dropMap H =
    replacementVertexInclusion (liftedDiagram H) (AsSmall.up.obj (op ⦋0⦌)) :=
  barZeroInclusion_drop H

example {F : SSet.{u}} (σ : (Functor.const SimplexCategoryᵒᵖ).obj F ⟶ H) :
    σ.app (op ⦋0⦌) ≫ barZeroInclusion H ≫ evaluationMap H =
      (diagonalConstantIso F).inv ≫ diagonalMap σ :=
  barZeroInclusion_evaluation_section σ

example : η.app (op ⦋0⦌) ≫ barZeroInclusion J = barZeroInclusion H ≫ barMap η :=
  barZeroInclusion_naturality η

example (b : |J.obj (op ⦋0⦌)|)
    (z : HomotopyFiber (SSet.toTop.map (η.app (op ⦋0⦌))).hom b) :
    (barZeroFiberMap η b z).1.1 = SSet.toTop.map (barZeroInclusion H) z.1.1 :=
  barZeroFiberMap_source η b z

example (b : |J.obj (op ⦋0⦌)|)
    (z : HomotopyFiber (SSet.toTop.map (η.app (op ⦋0⦌))).hom b) :
    (barZeroFiberMap η b z).1.2 = (SSet.toTop.map (barZeroInclusion J)).hom.comp z.1.2 :=
  barZeroFiberMap_path η b z

example (b : |J.obj (op ⦋0⦌)|)
    (z : HomotopyFiber (SSet.toTop.map (η.app (op ⦋0⦌))).hom b) :
    (zeroDiagonalFiberMap η b z).1.1 = SSet.toTop.map (zeroDiagonalInclusion H) z.1.1 :=
  zeroDiagonalFiberMap_source η b z

example (b : |J.obj (op ⦋0⦌)|)
    (z : HomotopyFiber (SSet.toTop.map (η.app (op ⦋0⦌))).hom b) :
    (zeroDiagonalFiberMap η b z).1.2 =
      (SSet.toTop.map (zeroDiagonalInclusion J)).hom.comp z.1.2 :=
  zeroDiagonalFiberMap_path η b z

example (b : |J.obj (op ⦋0⦌)|) : IsWeakHomotopyEquivalence (barZeroFiberMap η b) :=
  barZeroFiberMap_isWeakHomotopyEquivalence η h b

example (b : |J.obj (op ⦋0⦌)|) : IsWeakHomotopyEquivalence (zeroDiagonalFiberMap η b) :=
  zeroDiagonalFiberMap_isWeakHomotopyEquivalence η h b

example (b : |J.obj (op ⦋0⦌)|)
    (z : HomotopyFiber (SSet.toTop.map (η.app (op ⦋0⦌))).hom b) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (zeroDiagonalFiberMap η b) (x := z) rfl) :=
  (zeroDiagonalFiberMap_isWeakHomotopyEquivalence η h b).homotopy_bijective z 0

example (b : |J.obj (op ⦋0⦌)|)
    [IsEmpty (HomotopyFiber (SSet.toTop.map (η.app (op ⦋0⦌))).hom b)] :
    IsEmpty (HomotopyFiber (SSet.toTop.map (diagonalMap η)).hom
      (SSet.toTop.map (evaluationMap J) (SSet.toTop.map (barZeroInclusion J) b))) :=
  (zeroDiagonalFiberMap_isWeakHomotopyEquivalence η h b).isEmpty_target

example (x : (H.obj (op ⦋0⦌)) _⦋0⦌) :
    SSet.toTop.map (evaluationMap H)
      (SSet.toTop.map (barZeroInclusion H) (realizationPoint x)) =
        realizationPoint (X := diagonalSSet H) x :=
  evaluation_barZero_realizationPoint H x

end Tests.TwoSidedBarZeroFiber
