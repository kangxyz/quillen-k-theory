/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Fibration.Rows.EquivalenceJoint
import Quillen.Waldhausen.ExtensionCategory.HeterogeneousDetection

/-! # Actual endpoint and universal-property consumers of joint-data transport -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v' u'' v''
namespace Quillen.Tests.JointDataTransport
open Waldhausen Waldhausen.Fibration Waldhausen.Fibration.RowFactorization
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) (e : C ≌ D)
  (hF : IsExact V.cof V.weq W.cof W.weq e.functor)
  (hG : IsExact W.cof W.weq V.cof V.weq e.inverse)
  (T : JointData (NestedWeakEquivalences.refl V))

/-- The left endpoint keeps the specified original counit, without changing arrows. -/
theorem original_left_endpoint (f : Arrow D) :
    (JointData.ofExactEquivalence V W e hF hG T).inl.app f =
      (e.counitIso.app f.left).inv ≫ e.functor.map (T.inl.app (e.inverse.mapArrow.obj f)) := rfl

/-- The right endpoint projection retains both the original projection and counit. -/
theorem original_projection (f : Arrow D) :
    (JointData.ofExactEquivalence V W e hF hG T).projection.app f =
      e.functor.map (T.projection.app (e.inverse.mapArrow.obj f)) ≫
        (e.counitIso.app f.right).hom := rfl

/-- Transport factors the original arrow, including the transported endpoint maps. -/
theorem original_factorization (f : Arrow D) :
    (JointData.ofExactEquivalence V W e hF hG T).inl.app f ≫
      ((JointData.ofExactEquivalence V W e hF hG T).joint.obj f).obj.hom ≫
      (JointData.ofExactEquivalence V W e hF hG T).projection.app f = f.hom :=
  (JointData.ofExactEquivalence V W e hF hG T).factorization f

/-- The displayed endpoint maps are an actual coproduct cocone. -/
def original_coproduct (f : Arrow D) :
    IsColimit (BinaryCofan.mk
      ((JointData.ofExactEquivalence V W e hF hG T).inl.app f)
      ((JointData.ofExactEquivalence V W e hF hG T).inr.app f)) :=
  (JointData.ofExactEquivalence V W e hF hG T).coproduct f

include hF in
/-- Actual arrow-category pushouts are preserved by the original mapped arrows. -/
theorem original_arrow_pushout {A B E P : Arrow C} {i : A ⟶ B} {f : A ⟶ E}
    {g : B ⟶ P} {j : E ⟶ P} (hi : (ArrowCategory.waldhausenStructure V).cof i)
    (h : IsPushout i f g j) :
    IsPushout (e.functor.mapArrow.map i) (e.functor.mapArrow.map f)
      (e.functor.mapArrow.map g) (e.functor.mapArrow.map j) :=
  (ArrowCategory.mapArrow_exact V W hF).pushout hi h

/-- Two independently sized target categories detect the original relative cofibration. -/
theorem heterogeneous_relative_cof {E : Type u''} [Category.{v''} E]
    (U : Structure E) {F : C ⥤ D} {G : C ⥤ E}
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G)
    (detect : ∀ ⦃A B : C⦄ (f : A ⟶ B), W.cof (F.map f) → U.cof (G.map f) → V.cof f)
    {X Y : ExtensionCategory.Obj V} {f : X ⟶ Y}
    (hf : ExtensionCategory.cof W ((ExtensionCategory.postcompose V W hF).map f))
    (hg : ExtensionCategory.cof U ((ExtensionCategory.postcompose V U hG).map f)) :
    V.cof (ExtensionCategory.relativeMap V f) :=
  (ExtensionCategory.cof_of_postcompose_pair V W U hF hG detect hf hg).2
end Quillen.Tests.JointDataTransport
