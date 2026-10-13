/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Approximation.DualInverseImageLift

/-! # Original coarse lifts and K-zero consumers without fine reflection -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Quillen.Waldhausen
universe u v
namespace QuillenTest.DualInverseImageLift
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {W : Structure C} {Wd : Structure Cᵒᵖ} {V : Structure D} {Vd : Structure Dᵒᵖ}
  {U : Structure E} {Ud : Structure Eᵒᵖ}
  (hW : IsCompatibleDual W Wd) (hV : IsCompatibleDual V Vd)
  (hU : IsCompatibleDual U Ud) {F : C ⥤ D} {G : D ⥤ E}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hFd : IsExact Wd.cof Wd.weq Vd.cof Vd.weq F.op)
  (hG : IsExact V.cof V.weq U.cof U.weq G)
  (hGd : IsExact Vd.cof Vd.weq Ud.cof Ud.weq G.op)
  (hlift : ∀ {X : C} {Y : D} (f : Y ⟶ F.obj X),
    ∃ (X' : C) (i : X' ⟶ X) (p : Y ⟶ F.obj X'),
      Wd.cof.unop i ∧ V.weq p ∧ p ≫ F.map i = f)

include hF hG hlift in
/-- The actual original incoming triangle survives with weakness detected by G. -/
theorem original_coarse_lift {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    ∃ (X' : C) (i : X' ⟶ X) (p : Y ⟶ F.obj X'),
      Wd.cof.unop i ∧ U.weq (G.map p) ∧ p ≫ F.map i = f :=
  (dualApproximation_of_inverseImageLift hF hG hlift).lift f

include hW hV hU hFd hGd hlift in
/-- Actual incoming lifts and genuine joint data give unique original K-zero
preimages, without assuming that F reflects the fine weak class. -/
theorem original_KZero_unique_preimage [U.weq.HasTwoOutOfThreeProperty]
    (Jd : Fibration.RowFactorization.JointData (.refl Wd))
    (y : (Structure.withInverseImageWeak hG).K 0) :
    ∃! x : (Structure.withInverseImageWeak (hF.comp hG)).K 0,
      KMap (inverseImageComposite_exact hF hG) 0 x = y := by
  have hb := KMap_bijective_of_dualLift_inverseImage hW hV hU hF hFd hG hGd hlift Jd 0
  obtain ⟨x, hx⟩ := hb.surjective y
  exact ⟨x, hx, fun z hz => hb.injective (hz.trans hx.symm)⟩

include hW hV hU hFd hGd hlift in
/-- Equality of the unchanged original relative K-images is reflected in every degree. -/
theorem original_KMap_reflects_equality [U.weq.HasTwoOutOfThreeProperty]
    (Jd : Fibration.RowFactorization.JointData (.refl Wd)) (n : ℕ)
    (x y : (Structure.withInverseImageWeak (hF.comp hG)).K n) :
    KMap (inverseImageComposite_exact hF hG) n x = KMap (inverseImageComposite_exact hF hG) n y ↔ x
      = y :=
  (KMap_bijective_of_dualLift_inverseImage hW hV hU hF hFd hG hGd hlift Jd n).injective.eq_iff

end QuillenTest.DualInverseImageLift
