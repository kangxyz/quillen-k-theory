/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Duality.InverseImageWeak
import Quillen.Waldhausen.Fibration.Rows.JointRetarget
import Quillen.Waldhausen.Approximation.Dual

/-! # Dual approximation with genuine inverse-image weak classes

The same fine factorization supplies the relative factorization. Coarse joint
exactness is derived from the original fine joint data and saturation.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {W : Structure C} {Wd : Structure Cᵒᵖ} {V : Structure D} {Vd : Structure Dᵒᵖ}
  {U : Structure E} {Ud : Structure Eᵒᵖ}
  (hW : IsCompatibleDual W Wd) (hV : IsCompatibleDual V Vd)
  (hU : IsCompatibleDual U Ud) {F : C ⥤ D} {G : D ⥤ E}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hFd : IsExact Wd.cof Wd.weq Vd.cof Vd.weq F.op)
  (hG : IsExact V.cof V.weq U.cof U.weq G)
  (hGd : IsExact Vd.cof Vd.weq Ud.cof Ud.weq G.op)
  (h : HasDualApproximationProperty W V Wd.cof.unop F)

/-- Exactness for inverse-image weak classes uses the unchanged original map. -/
theorem inverseImageComposite_exact :
    IsExact (Structure.withInverseImageWeak (hF.comp hG)).cof
      (Structure.withInverseImageWeak (hF.comp hG)).weq
      (Structure.withInverseImageWeak hG).cof (Structure.withInverseImageWeak hG).weq F where
  zero := hF.zero
  cofibration := hF.cofibration
  weak _ hf := hf
  pushout := hF.pushout

include h in
/-- Reuse the original fine lift, including its literal factorization equation. -/
theorem HasDualApproximationProperty.inverseImageComposite :
    HasDualApproximationProperty (Structure.withInverseImageWeak (hF.comp hG))
      (Structure.withInverseImageWeak hG) Wd.cof.unop F where
  reflects _ hf := hf
  lift f := by
    obtain ⟨X, i, p, hi, hp, he⟩ := h.lift f
    exact ⟨X, i, p, hi, hG.weak p hp, he⟩

include hW hV hU hFd hGd h in
/-- Actual relative K-equivalence from fine incoming factorizations and fine joint data. -/
theorem KMap_bijective_of_dualApproximation_inverseImage
    [U.weq.HasTwoOutOfThreeProperty]
    (Jd : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl Wd))
    (n : ℕ) : Function.Bijective (KMap (inverseImageComposite_exact hF hG) n) := by
  let := hU.dual_saturated
  let : (Structure.inverseImageWeakNested (hFd.comp hGd)).coarse.weq.HasTwoOutOfThreeProperty :=
    Structure.withInverseImageWeak_twoOutOfThree (hFd.comp hGd)
  exact KMap_bijective_of_dualApproximation
    (hW.withInverseImageWeak hU (hF.comp hG) (hFd.comp hGd))
    (hV.withInverseImageWeak hU hG hGd)
    (inverseImageComposite_exact hF hG) (inverseImageComposite_exact hFd hGd)
    (h.inverseImageComposite hF hG)
    (Jd.toCoarse (Structure.inverseImageWeakNested (hFd.comp hGd))) n

end Quillen.Waldhausen
