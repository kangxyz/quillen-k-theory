import Quillen.Waldhausen.Functoriality.KMap

/-! # Original K-maps of genuinely exact equivalences

Both functors of the actual categorical equivalence must be exact. The inverse
identities follow from the actual unit and counit and canonical K-map functoriality.
No realization or K-equivalence conclusion is assumed.
-/
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
  exact (DFunLike.congr_fun (KMap_comp hF hG n) x).symm.trans
    (by simpa only [KMap_id, MonoidHom.id_apply] using DFunLike.congr_fun h x)

/-- The original inverse-functor K-map is a right inverse by the actual counit. -/
theorem KMap_exactEquivalence_right_inv (n : ℕ) (x : W.K n) :
    KMap hF n (KMap hG n x) = x := by
  have h := KMap_eq_of_iso (hG.comp hF) (IsExact.id W.cof W.weq) e.counitIso n
  exact (DFunLike.congr_fun (KMap_comp hG hF n) x).symm.trans
    (by simpa only [KMap_id, MonoidHom.id_apply] using DFunLike.congr_fun h x)

/-- A genuine exact equivalence induces the original all-degree K-equivalence. -/
def KEquivOfExactEquivalence (n : ℕ) : V.K n ≃* W.K n where
  toFun := KMap hF n
  invFun := KMap hG n
  left_inv := KMap_exactEquivalence_left_inv V W e hF hG n
  right_inv := KMap_exactEquivalence_right_inv V W e hF hG n
  map_mul' := (KMap hF n).map_mul

@[simp] theorem KEquivOfExactEquivalence_toMonoidHom (n : ℕ) :
    (KEquivOfExactEquivalence V W e hF hG n).toMonoidHom = KMap hF n := rfl

@[simp] theorem KEquivOfExactEquivalence_symm_toMonoidHom (n : ℕ) :
    (KEquivOfExactEquivalence V W e hF hG n).symm.toMonoidHom = KMap hG n := rfl

end Quillen.Waldhausen
