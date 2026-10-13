/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Cofinality.GeneralKZeroValue
public import Quillen.Waldhausen.GrothendieckGroup.Image

/-!
# The original image quotient is the actual coarse K-zero obstruction

The unchanged change-of-weak-equivalences KMap and the actual realized grading
map agree with the quotient by the original algebraic image, after the genuine
original Grothendieck K-zero comparison. Range inclusion and universe lowering
remain explicit in `coarseKZeroValueMap`.
-/
@[expose] public section

noncomputable section
open CategoryTheory
universe u v
namespace Quillen.Waldhausen.AlgebraicGrothendieck
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) {V : Structure D} (F : C ⥤ D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- Extending the original image-quotient object grading is the literal quotient map. -/
theorem lift_imageQuotientGrading :
    lift V (imageQuotientGrading W F hF) = QuotientAddGroup.mk' (map W F hF).range := by
  apply hom_ext V
  intro A
  exact lift_objectClass V (imageQuotientGrading W F hF) A

variable (T : FunctorialFactorization V.smallModel)

/-- The actual coarse object class retains the original Laurent or other target object grade. -/
theorem imageQuotient_coarseKZeroValueMap_objectClass (A : D) :
    (imageQuotientGrading W F hF).coarseKZeroValueMap T
      ((imageQuotientGrading W F hF).coarseStructure.kZeroObjectClass A) =
        Multiplicative.ofAdd
          (QuotientAddGroup.mk' (map W F hF).range (objectClass V A)) :=
  (imageQuotientGrading W F hF).coarseKZeroValueMap_objectClass T A

/-- On every original target K-zero class, the unchanged coarse obstruction equals the
original image quotient after the inverse of the genuine Grothendieck comparison. -/
theorem imageQuotientKZeroMap_eq :
    ((imageQuotientGrading W F hF).coarseKZeroValueMap T).comp
      (KMap (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested) 0) =
        (QuotientAddGroup.mk' (map W F hF).range).toMultiplicative.comp
          (grothendieckKZeroEquivOfSmallModel V).symm.toMonoidHom := by
  rw [(imageQuotientGrading W F hF).coarseKZeroValueMap_comp_changeWeak T,
    lift_imageQuotientGrading]

/-- The same original coarse value map is bijective for the actual image quotient. -/
theorem imageQuotient_coarseKZeroValueMap_bijective :
    Function.Bijective ((imageQuotientGrading W F hF).coarseKZeroValueMap T) := by
  refine ⟨(imageQuotientGrading W F hF).coarseKZeroValueMap_injective T, ?_⟩
  intro a
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective (map W F hF).range a.toAdd
  refine ⟨KMap (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested) 0
    (grothendieckKZeroEquivOfSmallModel V (Multiplicative.ofAdd x)), ?_⟩
  have he := DFunLike.congr_fun (imageQuotientKZeroMap_eq W F hF T)
    (grothendieckKZeroEquivOfSmallModel V (Multiplicative.ofAdd x))
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulEquiv.symm_apply_apply] at he
  exact he.trans (congrArg Multiplicative.ofAdd hx)

/-- The original target object loop has its exact quotient class after the actual KMap. -/
theorem imageQuotientKZeroMap_objectClass (A : D) :
    (imageQuotientGrading W F hF).coarseKZeroValueMap T
      (KMap (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested) 0
        (V.kZeroObjectClass A)) =
      Multiplicative.ofAdd
        (QuotientAddGroup.mk' (map W F hF).range (objectClass V A)) := by
  rw [KMap_kZeroObjectClass]
  exact imageQuotient_coarseKZeroValueMap_objectClass W F hF T A

end Quillen.Waldhausen.AlgebraicGrothendieck
