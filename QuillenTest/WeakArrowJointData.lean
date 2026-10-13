/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.WeakArrow.JointData

/-! Behavioral consumers of genuine opposite weak-arrow colimit reflection. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u v u' v'
namespace QuillenTest.WeakArrowJointData

open Quillen
open Waldhausen
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) (F : C ⥤ D)
  (hF : IsExact V.cof V.weq W.cof W.weq F)

include hF in
/-- Component zero objects make every original outgoing arrow literally unique. -/
theorem original_zero_arrows (X Y : (WeakArrow.Obj W F)ᵒᵖ)
    (hC : IsZero ((WeakArrow.source W F).op.obj X))
    (hD : IsZero ((WeakArrow.target W F).op.obj X)) (f g : X ⟶ Y) : f = g :=
  (WeakArrow.dual_isZero_of_components V W F hF X hC hD).eq_of_src f g

/-- Arbitrary component pushouts give the actual unique original descent map,
without a cofibration premise. -/
theorem original_unique_pushout_descent {A B E Q T : (WeakArrow.Obj W F)ᵒᵖ}
    (i : A ⟶ B) (f : A ⟶ E) (g : B ⟶ Q) (j : E ⟶ Q)
    (hC : IsPushout ((WeakArrow.source W F).op.map i) ((WeakArrow.source W F).op.map f)
      ((WeakArrow.source W F).op.map g) ((WeakArrow.source W F).op.map j))
    (hD : IsPushout ((WeakArrow.target W F).op.map i) ((WeakArrow.target W F).op.map f)
      ((WeakArrow.target W F).op.map g) ((WeakArrow.target W F).op.map j))
    (a : B ⟶ T) (b : E ⟶ T) (h : i ≫ a = f ≫ b) :
    ∃! m : Q ⟶ T, g ≫ m = a ∧ j ≫ m = b := by
  have hp := WeakArrow.dual_isPushout_of_components W F i f g j hC hD
  refine ⟨hp.desc a b h, ⟨hp.inl_desc _ _ _,hp.inr_desc _ _ _⟩, ?_⟩
  intro m hm
  exact hp.hom_ext (hm.1.trans (hp.inl_desc _ _ _).symm) (hm.2.trans (hp.inr_desc _ _ _).symm)

include hF in
/-- Component coproducts give unique original maps out of the unchanged cofan point. -/
theorem original_unique_coproduct_descent {A B T : (WeakArrow.Obj W F)ᵒᵖ}
    (s : BinaryCofan A B)
    (hC : IsColimit (BinaryCofan.mk ((WeakArrow.source W F).op.map s.inl)
      ((WeakArrow.source W F).op.map s.inr)))
    (hD : IsColimit (BinaryCofan.mk ((WeakArrow.target W F).op.map s.inl)
      ((WeakArrow.target W F).op.map s.inr))) (a : A ⟶ T) (b : B ⟶ T) :
    ∃! m : s.pt ⟶ T, s.inl ≫ m = a ∧ s.inr ≫ m = b := by
  let hs := WeakArrow.dualBinaryCofanIsColimitOfComponents V W F hF s hC hD
  refine ⟨BinaryCofan.IsColimit.desc hs a b,
    ⟨BinaryCofan.IsColimit.inl_desc hs _ _, BinaryCofan.IsColimit.inr_desc hs _ _⟩, ?_⟩
  intro m hm
  exact BinaryCofan.IsColimit.hom_ext hs
    (hm.1.trans (BinaryCofan.IsColimit.inl_desc hs _ _).symm)
    (hm.2.trans (BinaryCofan.IsColimit.inr_desc hs _ _).symm)



variable (Vd : Structure Cᵒᵖ) (Wd : Structure Dᵒᵖ)
  (hFd : IsExact Vd.cof Vd.weq Wd.cof Wd.weq F.op)
  (hW : IsCompatibleDual W Wd)
  (Tc : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl Vd))
  (Td : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl Wd))
  (compat : Tc.joint ⋙ ExtensionCategory.postcompose Vd Wd hFd ≅ F.op.mapArrow ⋙ Td.joint)
  (hinl : ∀ f, Td.inl.app (F.op.mapArrow.obj f) ≫ (compat.inv.app f).hom.left =
    F.op.map (Tc.inl.app f))
  (hinr : ∀ f, Td.inr.app (F.op.mapArrow.obj f) ≫ (compat.inv.app f).hom.left =
    F.op.map (Tc.inr.app f))
  (hproj : ∀ f, (compat.inv.app f).hom.right ≫ F.op.map (Tc.projection.app f) =
    Td.projection.app (F.op.mapArrow.obj f))

/-- The constructed opposite cylinder factors the unchanged original arrow. -/
theorem original_joint_factorization (f : Arrow (WeakArrow.Obj W F)ᵒᵖ) :
    (WeakArrow.dualJointData V W Vd Wd F hF hFd hW Tc Td compat hinl hinr hproj).inl.app f ≫
      ((WeakArrow.dualJointData V W Vd Wd F hF hFd hW Tc Td compat hinl hinr hproj).joint.obj
        f).obj.hom ≫
      (WeakArrow.dualJointData V W Vd Wd F hF hFd hW Tc Td compat hinl hinr hproj).projection.app f
        = f.hom :=
  (WeakArrow.dualJointData V W Vd Wd F hF hFd hW Tc Td compat hinl hinr hproj).factorization f

/-- The projection is genuinely weak on both unchanged original components. -/
theorem original_projection_components (f : Arrow (WeakArrow.Obj W F)ᵒᵖ) :
    Vd.weq ((WeakArrow.source W F).op.map
      ((WeakArrow.dualJointData V W Vd Wd F hF hFd hW Tc Td compat hinl hinr hproj).projection.app
        f)) ∧
    Wd.weq ((WeakArrow.target W F).op.map
      ((WeakArrow.dualJointData V W Vd Wd F hF hFd hW Tc Td compat hinl hinr hproj).projection.app
        f)) :=
  (WeakArrow.dualJointData V W Vd Wd F hF hFd hW Tc Td compat hinl hinr hproj).weak f

/-- Exactness proves the actual relative pushout comparison cofibrant. -/
theorem original_joint_relative_cof {X Y : Arrow (WeakArrow.Obj W F)ᵒᵖ} (f : X ⟶ Y)
    (hf : (ArrowCategory.waldhausenStructure
      (WeakArrow.dualWaldhausenStructure V W Vd Wd F hF hFd hW)).cof f) :
    (WeakArrow.dualWaldhausenStructure V W Vd Wd F hF hFd hW).cof
      (ExtensionCategory.relativeMap _
        ((WeakArrow.dualJointData V W Vd Wd F hF hFd hW Tc Td compat hinl hinr hproj).joint.map f))
          :=
  ((WeakArrow.dualJointData V W Vd Wd F hF hFd hW Tc Td compat hinl hinr hproj).exact.cofibration f
    hf).2

/-- The endpoint coproduct has unique descent along the actual constructed maps. -/
theorem original_joint_coproduct_unique (f : Arrow (WeakArrow.Obj W F)ᵒᵖ)
    {T : (WeakArrow.Obj W F)ᵒᵖ}
    (a b : ((WeakArrow.dualJointData V W Vd Wd F hF hFd hW Tc Td compat hinl hinr hproj).joint.obj
      f).obj.left ⟶ T)
    (hl : (WeakArrow.dualJointData V W Vd Wd F hF hFd hW Tc Td compat hinl hinr hproj).inl.app f ≫ a
      =
      (WeakArrow.dualJointData V W Vd Wd F hF hFd hW Tc Td compat hinl hinr hproj).inl.app f ≫ b)
    (hr : (WeakArrow.dualJointData V W Vd Wd F hF hFd hW Tc Td compat hinl hinr hproj).inr.app f ≫ a
      =
      (WeakArrow.dualJointData V W Vd Wd F hF hFd hW Tc Td compat hinl hinr hproj).inr.app f ≫ b) :
        a = b :=
  BinaryCofan.IsColimit.hom_ext
    ((WeakArrow.dualJointData V W Vd Wd F hF hFd hW Tc Td compat hinl hinr hproj).coproduct f) hl hr
end QuillenTest.WeakArrowJointData
