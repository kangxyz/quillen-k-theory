/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeEvaluationCells

/-! Six original cells determine every value on the full four-edge reference tree. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
open CutOpenCarrier
variable {V W T : Model.{u}} (E : V ⟶ W) (J : W ⟶ T)

theorem funext_cells {B : Type u} (a b : space E J → B)
    (hp : ∀ y, a (SSet.toTop.map (plusVertex E J) y) =
      b (SSet.toTop.map (plusVertex E J) y))
    (hm : ∀ y, a (SSet.toTop.map (minusVertex E J) y) =
      b (SSet.toTop.map (minusVertex E J) y))
    (h12 : ∀ y t, a (realizedEdge (edge12 E J) (y, t)) =
      b (realizedEdge (edge12 E J) (y, t)))
    (h01 : ∀ y t, a (realizedEdge (edge01 E J) (y, t)) =
      b (realizedEdge (edge01 E J) (y, t)))
    (h03 : ∀ y t, a (realizedEdge (edge03 E J) (y, t)) =
      b (realizedEdge (edge03 E J) (y, t)))
    (h34 : ∀ y t, a (realizedEdge (edge34 E J) (y, t)) =
      b (realizedEdge (edge34 E J) (y, t))) : a = b := by
  have hv1 (y : |parameterSSet E|) :
      a (SSet.toTop.map (oneVertex E J) y) = b (SSet.toTop.map (oneVertex E J) y) := by
    simpa only [realizedEdge_zero, edge12_zero] using h12 y 0
  have hv0 (y : |parameterSSet E|) :
      a (SSet.toTop.map (zeroVertex E J) y) = b (SSet.toTop.map (zeroVertex E J) y) := by
    simpa only [realizedEdge_zero, edge01_zero] using h01 y 0
  have hv3 (y : |parameterSSet E|) :
      a (SSet.toTop.map (threeVertex E J) y) = b (SSet.toTop.map (threeVertex E J) y) := by
    simpa only [realizedEdge_zero, edge34_zero] using h34 y 0
  have hfirst : (fun z ↦ a (SSet.toTop.map (firstInTree E J) z)) =
      (fun z ↦ b (SSet.toTop.map (firstInTree E J) z)) := by
    apply SetDescent.funext (𝟙 _) (attachment E J)
    · rintro ⟨y, ⟨t⟩⟩
      have h := h12 y t
      rw [edge12, realizedEdge_comp] at h
      exact h
    · intro y
      simpa only [oneVertex, realized_comp, firstOne,
        first, second, third, simplicial, space] using hv1 y
    · intro y
      simpa only [plusVertex, realized_comp, firstPlus,
        first, second, third, simplicial, space] using hp y
  have hsecond : (fun z ↦ a (SSet.toTop.map (secondInTree E J) z)) =
      (fun z ↦ b (SSet.toTop.map (secondInTree E J) z)) := by
    apply SetDescent.funext (𝟙 _) (firstOne E J)
    · rintro ⟨y, ⟨t⟩⟩
      have h := h01 y t
      rw [edge01, realizedEdge_comp] at h
      exact h
    · intro y
      simpa only [zeroVertex, realized_comp, secondZero,
        first, second, third, simplicial, space] using hv0 y
    · intro y
      simpa only [firstInTree, realized_comp, firstInSecond,
        first, second, third, simplicial, space] using congrFun hfirst y
  have hthird : (fun z ↦ a (SSet.toTop.map (thirdInTree E J) z)) =
      (fun z ↦ b (SSet.toTop.map (thirdInTree E J) z)) := by
    apply SetDescent.funext (secondZero E J) (𝟙 _)
    · rintro ⟨y, ⟨t⟩⟩
      have h := h03 y t
      rw [edge03, realizedEdge_comp] at h
      exact h
    · intro y
      simpa only [secondInTree, realized_comp, secondInThird,
        first, second, third, simplicial, space] using congrFun hsecond y
    · intro y
      simpa only [threeVertex, realized_comp, thirdThree,
        first, second, third, simplicial, space] using hv3 y
  apply SetDescent.funext (thirdThree E J) (attachment E J)
  · intro z
    exact h34 z.1 z.2.down
  · intro y
    exact congrFun hthird y
  · exact hm

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
