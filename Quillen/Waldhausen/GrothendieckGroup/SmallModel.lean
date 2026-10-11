/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.GrothendieckGroup.Functor
public import Quillen.Waldhausen.SmallModel.Basic
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-! # Universe lifting preserves the original classical Waldhausen presentation

The actual exact up/down functors between the original category and its
existing common-universe model induce mutually inverse maps on the original
object/weak-arrow/cofibration-pushout quotient. Every original generator is retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory
universe u v
namespace Quillen.Waldhausen.AlgebraicGrothendieck
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The actual downward presentation map is a left inverse to the actual upward map. -/
theorem smallModel_down_comp_up :
    (map W.smallModel (AsSmall.down : SmallModel C ⥤ C) W.smallModel_down_exact).comp
      (map W (AsSmall.up : C ⥤ SmallModel C) W.smallModel_up_exact) =
        AddMonoidHom.id (Group W) := by
  apply hom_ext W
  intro A
  simp only [AddMonoidHom.comp_apply, map_objectClass, AddMonoidHom.id_apply]
  rfl

/-- The actual upward presentation map is a left inverse to the actual downward map. -/
theorem smallModel_up_comp_down :
    (map W (AsSmall.up : C ⥤ SmallModel C) W.smallModel_up_exact).comp
      (map W.smallModel (AsSmall.down : SmallModel C ⥤ C) W.smallModel_down_exact) =
        AddMonoidHom.id (Group W.smallModel) := by
  apply hom_ext W.smallModel
  intro A
  simp only [AddMonoidHom.comp_apply, map_objectClass, AddMonoidHom.id_apply]
  rfl

/-- The actual original algebraic presentation agrees with its genuine common-universe model. -/
def smallModelGrothendieckEquiv : Group W ≃+ Group W.smallModel where
  toFun := map W (AsSmall.up : C ⥤ SmallModel C) W.smallModel_up_exact
  invFun := map W.smallModel (AsSmall.down : SmallModel C ⥤ C) W.smallModel_down_exact
  left_inv := DFunLike.congr_fun (smallModel_down_comp_up W)
  right_inv := DFunLike.congr_fun (smallModel_up_comp_down W)
  map_add' := (map W AsSmall.up W.smallModel_up_exact).map_add

/-- The universe-lifting equivalence retains the original upward object class. -/
@[simp] theorem smallModelGrothendieckEquiv_objectClass (A : C) :
    smallModelGrothendieckEquiv W (objectClass W A) =
      objectClass W.smallModel (AsSmall.up.obj A) :=
  map_objectClass W AsSmall.up W.smallModel_up_exact A

/-- Its inverse retains the original downward object class. -/
@[simp] theorem smallModelGrothendieckEquiv_symm_objectClass (A : SmallModel C) :
    (smallModelGrothendieckEquiv W).symm (objectClass W.smallModel A) =
      objectClass W (AsSmall.down.obj A) :=
  map_objectClass W.smallModel AsSmall.down W.smallModel_down_exact A

variable {D : Type u} [Category.{v} D] (V : Structure D) (F : C ⥤ D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- The original universe-lifting algebraic equivalence respects every original exact functor. -/
theorem smallModelGrothendieckEquiv_natural (a : Group W) :
    smallModelGrothendieckEquiv V (map W F hF a) =
      map W.smallModel (smallModelFunctor F) hF.smallModel
        (smallModelGrothendieckEquiv W a) := by
  have h : (smallModelGrothendieckEquiv V : Group V →+ Group V.smallModel).comp (map W F hF) =
      (map W.smallModel (smallModelFunctor F) hF.smallModel).comp
        (smallModelGrothendieckEquiv W : Group W →+ Group W.smallModel) := by
    apply hom_ext W
    intro A
    simp only [AddMonoidHom.comp_apply, map_objectClass,
      AddMonoidHom.coe_coe, smallModelGrothendieckEquiv_objectClass]
    rfl
  exact DFunLike.congr_fun h a

end Quillen.Waldhausen.AlgebraicGrothendieck
