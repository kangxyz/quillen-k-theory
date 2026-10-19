/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.ZigzagSequentializationNaturality
public import Quillen.Topology.Prespectrum.ZigzagSequentializationLinearGrowth

/-! Regression tests for the original pushout recurrence and its entire cylinder. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open Quillen.LoopPrespectrum Quillen.LoopPrespectrum.ZigzagSequentialization
universe u
namespace QuillenTest.ZigzagSequentialization
variable (E : ℕ → Quillen.LoopPrespectrum.{u}) (f : ∀ n, E n ⟶ E (n + 1))

/-- An identity backward leg gives a genuine retraction from the second canonical pushout. -/
def secondStageCollapse :
    stage E (fun n ↦ E (n + 1)) f (fun n ↦ 𝟙 (E (n + 1))) 2 ⟶ E 2 :=
  HomotopyPushout.desc (𝟙 (E 1)) (f 1) (f 1) (𝟙 (E 2))
    ((Homotopy.refl (f 1)).cast (Category.id_comp _).symm (Category.comp_id _).symm)

/-- The second comparison really uses the right inclusion of the displayed pushout. -/
example : comparison E (fun n ↦ E (n + 1)) f (fun n ↦ 𝟙 (E (n + 1))) 2 ≫
    secondStageCollapse E f = 𝟙 (E 2) :=
  HomotopyPushout.inr_desc _ _ _ _ _

/-- Every value of the original overlap cylinder survives the exact collapse prescription. -/
example (k : ℕ) (s : unitInterval) (x : (E 1).space k) :
    (secondStageCollapse E f).map k
      (HomotopyPushout.cylinder (𝟙 (E 1)) (f 1) k (s, x)) = (f 1).map k x := rfl

/-- The initial whole-track telescope comparison preserves the original initial inclusion. -/
example :
    Telescope.inclusion E f 0 ≫ telescopeMap E (fun n ↦ E (n + 1)) f
      (fun n ↦ 𝟙 (E (n + 1))) f
      (fun n ↦ (Homotopy.refl (f n)).cast rfl (Category.comp_id _).symm) =
    Telescope.inclusion (stage E (fun n ↦ E (n + 1)) f (fun n ↦ 𝟙 (E (n + 1))))
      (transition E (fun n ↦ E (n + 1)) f (fun n ↦ 𝟙 (E (n + 1)))) 0 := by
  rw [inclusion_telescopeMap, comparison_zero, Category.id_comp]

end QuillenTest.ZigzagSequentialization
