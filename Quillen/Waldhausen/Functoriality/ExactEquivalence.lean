/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Functoriality.KMap

/-! # Original K-maps of genuinely exact equivalences

Both functors of the actual categorical equivalence must be exact. The inverse
identities follow from the actual unit and counit and canonical K-map functoriality.
No realization or K-equivalence conclusion is assumed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u v
namespace Quillen.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) (e : C ≌ D)
  (hF : IsExact V.cof V.weq W.cof W.weq e.functor)
  (hG : IsExact W.cof W.weq V.cof V.weq e.inverse)

/-- The original inverse-functor K-map is a left inverse by the actual unit. -/
theorem KMap_exactEquivalence_left_inv (n : ℕ) (x : V.K n) :
    KMap hG n (KMap hF n x) = x := by
  have h := KMap_eq_of_iso (hF.comp hG) (IsExact.id V.cof V.weq) e.unitIso.symm n
  exact (DFunLike.congr_fun (KMap_comp_KMap hF hG n).symm x).symm.trans
    (by simpa only [KMap_id, MonoidHom.id_apply] using DFunLike.congr_fun h x)

/-- The original inverse-functor K-map is a right inverse by the actual counit. -/
theorem KMap_exactEquivalence_right_inv (n : ℕ) (x : W.K n) :
    KMap hF n (KMap hG n x) = x := by
  have h := KMap_eq_of_iso (hG.comp hF) (IsExact.id W.cof W.weq) e.counitIso n
  exact (DFunLike.congr_fun (KMap_comp_KMap hG hF n).symm x).symm.trans
    (by simpa only [KMap_id, MonoidHom.id_apply] using DFunLike.congr_fun h x)

/-- A genuine exact equivalence induces the original all-degree K-equivalence. -/
def KEquivOfExactEquivalence (n : ℕ) : V.K n ≃* W.K n where
  toFun := KMap hF n
  invFun := KMap hG n
  left_inv := KMap_exactEquivalence_left_inv V W e hF hG n
  right_inv := KMap_exactEquivalence_right_inv V W e hF hG n
  map_mul' := (KMap hF n).map_mul

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem KEquivOfExactEquivalence_coe (n : ℕ) :
    (↑(KEquivOfExactEquivalence V W e hF hG n) : V.K n →* W.K n) = KMap hF n := rfl


/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem KEquivOfExactEquivalence_symm_coe (n : ℕ) :
    (↑(KEquivOfExactEquivalence V W e hF hG n).symm : W.K n →* V.K n) = KMap hG n := rfl


end Quillen.Waldhausen
