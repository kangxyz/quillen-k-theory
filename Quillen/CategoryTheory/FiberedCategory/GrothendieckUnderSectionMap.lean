/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.FiberedCategory.GrothendieckUnderSections

/-! Actual vertical maps and strict reindexing of the original restricted sections. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory
open Quillen.CategoryTheory.StrictSections Quillen.CategoryTheory.GrothendieckSections
universe u v u' v'
namespace Quillen.CategoryTheory.GrothendieckUnderSections
variable {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'}) (R : C)

/-- Original fiber transitions are natural in every vertical section map. -/
theorem originalArrowTransition_naturality (A : C)
    {s t : underCocartesian (Pseudofunctor.Grothendieck.forget F) A} (α : s ⟶ t)
    {i k : Under A} (f : i ⟶ k) :
    (F.map f.right.toLoc).toFunctor.map ((originalEvaluationAt F A i).map α) ≫
        originalArrowTransition F A t f =
      originalArrowTransition F A s f ≫ (originalEvaluationAt F A k).map α := by
  have hs : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian f.right
      (s.obj.val.map f) := s.property f
  have ht : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian f.right
      (t.obj.val.map f) := t.property f
  exact GrothendieckFiber.liftedMap_naturality F f.right
    ((cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) (Under.forget A) i).map α)
    ((cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) (Under.forget A) k).map α)
    (s.obj.val.map f) (t.obj.val.map f) (α.hom.val.naturality f).symm

attribute [local simp] PrelaxFunctor.map₂_eqToHom in
private theorem square_of_fiber_square {A B : C} (f : A ⟶ B)
    {a b : F.obj ⟨A⟩} {c d : F.obj ⟨B⟩} (α : a ⟶ b) (β : c ⟶ d)
    (p : (F.map f.toLoc).toFunctor.obj a ⟶ c)
    (q : (F.map f.toLoc).toFunctor.obj b ⟶ d)
    (h : (F.map f.toLoc).toFunctor.map α ≫ q = p ≫ β) :
    (GrothendieckFiber.inclusion F A).map α ≫
        (⟨f, q⟩ : (⟨A, b⟩ : Pseudofunctor.Grothendieck F) ⟶ ⟨B, d⟩) =
      (⟨f, p⟩ : (⟨A, a⟩ : Pseudofunctor.Grothendieck F) ⟶ ⟨B, c⟩) ≫
        (GrothendieckFiber.inclusion F B).map β := by
  refine Pseudofunctor.Grothendieck.Hom.ext (F := F) _ _ ?_ ?_
  · simp [GrothendieckFiber.inclusion]
  simp only [GrothendieckFiber.inclusion,
    Pseudofunctor.Grothendieck.categoryStruct_comp_fiber]
  simp only [Quiver.Hom.id_toLoc, Cat.Hom.id_toFunctor, Functor.id_obj,
    Pseudofunctor.Grothendieck.categoryStruct_comp_base, Quiver.Hom.comp_toLoc,
    F.mapComp_id_left_hom_app, Strict.leftUnitor_eqToIso, eqToIso.hom,
    PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
    Functor.map_comp, Category.assoc, eqToHom_trans_assoc, F.mapComp_id_right_hom_app,
    Strict.rightUnitor_eqToIso, NatTrans.naturality_assoc, Functor.id_map,
    Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
  simp only [← Cat.Hom.toNatIso_inv, ← Cat.Hom.toNatIso_hom,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  exact congrArg (fun k => _ ≫ k) h

/-- Every original vertical fiber map gives the unchanged vertical map of restricted sections. -/
def sectionMap (a : Under R)
    {s t : underCocartesian (Pseudofunctor.Grothendieck.forget F) a.right} (α : s ⟶ t) :
    sectionFunctor F R a s ⟶ sectionFunctor F R a t where
  app i := (GrothendieckFiber.inclusion (pseudofunctor F R) i.right).map
    ((originalEvaluationAt F a.right ((Under.post (Under.forget R)).obj i)).map α)
  naturality {i k} f := by
    exact (square_of_fiber_square (pseudofunctor F R) f.right _ _ _ _
      (originalArrowTransition_naturality F a.right α
        ((Under.post (Under.forget R)).map f))).symm

/-- Restriction sends actual sections and their actual vertical maps to the fixed-base sections. -/
def underFunctor (a : Under R) :
    underCocartesian (Pseudofunctor.Grothendieck.forget F) a.right ⥤
      underCocartesian (Pseudofunctor.Grothendieck.forget (pseudofunctor F R)) a where
  obj := restrictedSection F R a
  map α := ObjectProperty.homMk ⟨sectionMap F R a α, by
    apply IsHomLift.of_fac'
      ((Functor.whiskeringRight (Under a)
        (Pseudofunctor.Grothendieck (pseudofunctor F R)) (Under R)).obj
          (Pseudofunctor.Grothendieck.forget (pseudofunctor F R)))
      (𝟙 (Under.forget a)) _ (sectionFunctor_comp F R a _) (sectionFunctor_comp F R a _)
    apply NatTrans.ext
    funext i
    simp only [eqToHom_refl, NatTrans.id_app, Category.comp_id]
    rfl⟩
  map_id s := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    apply NatTrans.ext
    funext i
    simp [sectionMap]
    rfl
  map_comp α β := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    apply NatTrans.ext
    funext i
    simp [sectionMap]
    rfl

/-- The original coefficient reindexing square is literal on restricted sections and maps. -/
theorem underFunctor_naturality {a b : Under R} (f : a ⟶ b) :
    underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f.right ⋙
        underFunctor F R b =
      underFunctor F R a ⋙
        underCocartesianReindex (Pseudofunctor.Grothendieck.forget (pseudofunctor F R)) f := by
  rfl

end Quillen.CategoryTheory.GrothendieckUnderSections
