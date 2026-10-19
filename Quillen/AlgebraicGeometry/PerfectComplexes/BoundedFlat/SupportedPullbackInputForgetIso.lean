/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedPullbackForgetIso
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationInputRoutes

/-! # The whole original geometric input square after forgetting support

The two original geometric composition isomorphisms and the intervening equality transport
are retained as whole isomorphisms through the actual support inclusion. The resulting
identity is before evaluation, selected-zero normalization, or realization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
attribute [local irreducible] boundedFlatPerfectSupportedPullbackCompIso
  boundedFlatPerfectPullbackCompIso

private theorem rightTriple {E F G : Type*} [Category* E] [Category* F] [Category* G]
    {F₀ F₁ F₂ F₃ : E ⥤ F} (e₀ : F₀ ≅ F₁) (e₁ : F₁ ≅ F₂) (e₂ : F₂ ≅ F₃)
    (J : F ⥤ G) (r₀ : F₀ ⋙ J ≅ F₁ ⋙ J) (r₁ : F₁ ⋙ J ≅ F₂ ⋙ J)
    (r₂ : F₂ ⋙ J ≅ F₃ ⋙ J)
    (h₀ : isoWhiskerRight e₀ J = r₀) (h₁ : isoWhiskerRight e₁ J = r₁)
    (h₂ : isoWhiskerRight e₂ J = r₂) :
    isoWhiskerRight (e₀ ≪≫ e₁ ≪≫ e₂) J = r₀ ≪≫ r₁ ≪≫ r₂ := by
  rw [isoWhiskerRight_trans, isoWhiskerRight_trans, h₀, h₁, h₂]

private theorem leftTriple {E F G : Type*} [Category* E] [Category* F] [Category* G]
    (I : E ⥤ F) {F₀ F₁ F₂ F₃ : F ⥤ G}
    (e₀ : F₀ ≅ F₁) (e₁ : F₁ ≅ F₂) (e₂ : F₂ ≅ F₃) :
    isoWhiskerLeft I (e₀ ≪≫ e₁ ≪≫ e₂) =
      isoWhiskerLeft I e₀ ≪≫ isoWhiskerLeft I e₁ ≪≫ isoWhiskerLeft I e₂ := rfl

private theorem leftInput {J : Type*} [Category* J] {E F G H : Scheme.{u}}
    (p : E ⟶ F) (q : G ⟶ H) (a : G ⟶ E) (b : H ⟶ F) (h : a ≫ p = q ≫ b)
    (I : J ⥤ BoundedFlatPerfect F) :
    isoWhiskerLeft I (pullbackInputSquareIso p q a b h) =
      isoWhiskerLeft I (boundedFlatPerfectPullbackCompIso a p).symm ≪≫
        isoWhiskerLeft I (eqToIso (congrArg boundedFlatPerfectPullback h)) ≪≫
        isoWhiskerLeft I (boundedFlatPerfectPullbackCompIso q b) :=
  leftTriple I
    (F₀ := boundedFlatPerfectPullback p ⋙ boundedFlatPerfectPullback a)
    (F₁ := boundedFlatPerfectPullback (a ≫ p))
    (F₂ := boundedFlatPerfectPullback (q ≫ b))
    (F₃ := boundedFlatPerfectPullback b ⋙ boundedFlatPerfectPullback q)
    (boundedFlatPerfectPullbackCompIso a p).symm
    (eqToIso (congrArg boundedFlatPerfectPullback h))
    (boundedFlatPerfectPullbackCompIso q b)

/-- The entire independent supported geometric input comparison has its ambient forgetful image.
-/
theorem supportedPullbackInputSquareIso_forget {A B C D : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b) :
    isoWhiskerRight (supportedPullbackInputSquareIso p q a b h)
        (tensorCoefficientSupportedForget C.obj.hom) =
      isoWhiskerLeft (tensorCoefficientSupportedForget B.obj.hom)
        (pullbackInputSquareIso p.hom.right q.hom.right a.hom.right b.hom.right
          (congrArg (fun f : C ⟶ B => f.hom.right) h)) := by
  have he : a.hom.right ≫ p.hom.right = q.hom.right ≫ b.hom.right :=
    congrArg (fun f : C ⟶ B => f.hom.right) h
  have hr := rightTriple
    (F₀ := boundedFlatPerfectSupportedPullback p ⋙ boundedFlatPerfectSupportedPullback a)
    (F₁ := boundedFlatPerfectSupportedPullback (a ≫ p))
    (F₂ := boundedFlatPerfectSupportedPullback (q ≫ b))
    (F₃ := boundedFlatPerfectSupportedPullback b ⋙ boundedFlatPerfectSupportedPullback q)
    (boundedFlatPerfectSupportedPullbackCompIso a p).symm
    (eqToIso (congrArg boundedFlatPerfectSupportedPullback h))
    (boundedFlatPerfectSupportedPullbackCompIso q b)
    (tensorCoefficientSupportedForget C.obj.hom)
    (isoWhiskerLeft (tensorCoefficientSupportedForget B.obj.hom)
      (boundedFlatPerfectPullbackCompIso a.hom.right p.hom.right).symm)
    (isoWhiskerLeft (tensorCoefficientSupportedForget B.obj.hom)
      (eqToIso (congrArg boundedFlatPerfectPullback he)))
    (isoWhiskerLeft (tensorCoefficientSupportedForget B.obj.hom)
      (boundedFlatPerfectPullbackCompIso q.hom.right b.hom.right))
    (congrArg Iso.symm (boundedFlatPerfectSupportedPullbackCompIso_forget a p))
    (supportedPullbackEquality_forget_iso h)
    (boundedFlatPerfectSupportedPullbackCompIso_forget q b)
  have hl := leftInput p.hom.right q.hom.right a.hom.right b.hom.right he
    (tensorCoefficientSupportedForget B.obj.hom)
  exact hr.trans hl.symm

/-- Every actual bounded-flat component follows from the whole geometric comparison. -/
theorem supportedPullbackInputSquareIso_forget_hom_app {A B C D : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)
    (K : (boundedFlatPerfectSupported B.obj.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget C.obj.hom).map
        ((supportedPullbackInputSquareIso p q a b h).hom.app K) =
      (pullbackInputSquareIso p.hom.right q.hom.right a.hom.right b.hom.right
        (congrArg (fun f : C ⟶ B => f.hom.right) h)).hom.app
          ((tensorCoefficientSupportedForget B.obj.hom).obj K) :=
  NatTrans.congr_app (congrArg Iso.hom (supportedPullbackInputSquareIso_forget p q a b h)) K

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
