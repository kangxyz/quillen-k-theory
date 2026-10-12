/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.CategoryTheory.GroupCompletion.SwitchMiddle

/-! # Coherent descent of the switch middle functor -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalLeftAction
namespace Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
attribute [local instance] firstCoordinateLeftAction
/-- The pure braid coherence of the middle lineator. -/
lemma switchMiddleShuffle_associativity (s t A B : C) :
    switchMiddleShuffle (s ⊗ t) A B ≫ ((α_ s t B).hom ⊗ₘ (α_ s t A).hom) =
    (α_ s t ((B ⊗ A) ⊗ (s ⊗ t))).hom ≫
      s ◁ (t ◁ ((B ⊗ A) ◁ (β_ t s).inv ≫ (α_ (B ⊗ A) t s).inv) ≫
        (α_ t ((B ⊗ A) ⊗ t) s).inv ≫ switchMiddleShuffle t A B ▷ s) ≫
      switchMiddleShuffle s (t ⊗ A) (t ⊗ B) := by
  let pre := (α_ s t ((B ⊗ A) ⊗ (s ⊗ t))).hom ≫
    s ◁ (t ◁ (α_ B A (s ⊗ t)).hom)
  let post := (α_ s t (B ⊗ ((s ⊗ t) ⊗ A))).inv ≫
    (α_ (s ⊗ t) B ((s ⊗ t) ⊗ A)).inv ≫
      ((α_ s t B).hom ⊗ₘ (α_ s t A).hom)
  calc
    _ = pre ≫ s ◁ (t ◁ (B ◁ (β_ A (s ⊗ t)).hom)) ≫ post := by
      dsimp [pre, post, switchMiddleShuffle]
      monoidal
    _ = pre ≫ s ◁ (t ◁ (B ◁ (A ◁ (β_ t s).inv ≫
        (β_ A (t ⊗ s)).hom ≫ (β_ t s).hom ▷ A))) ≫ post := by
      rw [braiding_naturality_right_assoc]
      simp only [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight, Category.comp_id]
    _ = _ := by
      dsimp [pre, post, switchMiddleShuffle]
      rw [braiding_tensor_right_hom A t s, braiding_tensor_left_hom t A s]
      simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
      monoidal
/-- The middle denominator construction respects the action associator. -/
lemma switchMiddleLineator_associativity (X : D) (s t : C) (A : C × C) :
    switchMiddleLineator X (s ⊗ t) A ≫ (switchMiddlePair X).map (αₗ s t A).hom =
      (αₗ s t ((switchMiddlePair X).obj A)).hom ≫
        s ⊴ₗ switchMiddleLineator X t A ≫ switchMiddleLineator X s (t ⊙ₗ A) := by
  apply Prod.ext
  · change 𝟙 _ ≫ (α_ s t A.2).hom = (α_ s t A.2).hom ≫ s ◁ 𝟙 _ ≫ 𝟙 _
    simp
  · change
      mkHom (X := ((A.2 ⊗ A.1) ⊗ (s ⊗ t), A.2 ⊙ₗ X))
        (Y := (((s ⊗ t) ⊗ A.2) ⊗ ((s ⊗ t) ⊗ A.1), ((s ⊗ t) ⊗ A.2) ⊙ₗ X))
        (s ⊗ t) (switchMiddleShuffle (s ⊗ t) A.1 A.2) (αₗ (s ⊗ t) A.2 X).inv ≫
      ActionLocalization.ofHom
        (X := (((s ⊗ t) ⊗ A.2) ⊗ ((s ⊗ t) ⊗ A.1), ((s ⊗ t) ⊗ A.2) ⊙ₗ X))
        (Y := ((s ⊗ (t ⊗ A.2)) ⊗ (s ⊗ (t ⊗ A.1)), (s ⊗ (t ⊗ A.2)) ⊙ₗ X))
        ((α_ s t A.2).hom ⊗ₘ (α_ s t A.1).hom, (α_ s t A.2).hom ⊵ₗ X) =
      (secondFiberHom (A.2 ⊙ₗ X) ((A.2 ⊗ A.1) ◁ (β_ t s).inv) ≫
        secondFiberHom (A.2 ⊙ₗ X) (α_ (A.2 ⊗ A.1) t s).inv) ≫
      (firstCoordinateTranslation s).map
        (mkHom (X := ((A.2 ⊗ A.1) ⊗ t, A.2 ⊙ₗ X))
          (Y := ((t ⊗ A.2) ⊗ (t ⊗ A.1), (t ⊗ A.2) ⊙ₗ X)) t
            (switchMiddleShuffle t A.1 A.2) (αₗ t A.2 X).inv) ≫
      mkHom (X := (((t ⊗ A.2) ⊗ (t ⊗ A.1)) ⊗ s, (t ⊗ A.2) ⊙ₗ X))
        (Y := ((s ⊗ (t ⊗ A.2)) ⊗ (s ⊗ (t ⊗ A.1)), (s ⊗ (t ⊗ A.2)) ⊙ₗ X)) s
        (switchMiddleShuffle s (t ⊗ A.1) (t ⊗ A.2)) (αₗ s (t ⊗ A.2) X).inv
    rw [firstCoordinateTranslation_mkHom, secondFiberHom_comp]
    unfold mkHom secondFiberHom
    rw [ActionLocalization.mkHom_comp_ofHom, ← Category.assoc]
    erw [ActionLocalization.ofHom_comp_mkHom]
    change ActionLocalization.mkHom _ =
      ActionLocalization.mkHom (ActionLocalization.HomRep.comp _ _)
    apply congrArg ActionLocalization.mkHom
    apply congrArg (ActionLocalization.HomRep.mk (s ⊗ t))
    apply Prod.ext
    · dsimp only [ActionLocalization.HomRep.comp, CategoryTheory.prod_comp]
      change switchMiddleShuffle (s ⊗ t) A.1 A.2 ≫
          ((α_ s t A.2).hom ⊗ₘ (α_ s t A.1).hom) =
        (α_ s t ((A.2 ⊗ A.1) ⊗ (s ⊗ t))).hom ≫
          s ◁ (t ◁ ((A.2 ⊗ A.1) ◁ (β_ t s).inv ≫ (α_ (A.2 ⊗ A.1) t s).inv) ≫
            (α_ t ((A.2 ⊗ A.1) ⊗ t) s).inv ≫ switchMiddleShuffle t A.1 A.2 ▷ s) ≫
          switchMiddleShuffle s (t ⊗ A.1) (t ⊗ A.2)
      exact switchMiddleShuffle_associativity s t A.1 A.2
    · change (αₗ (s ⊗ t) A.2 X).inv ≫ (α_ s t A.2).hom ⊵ₗ X =
        (αₗ s t (A.2 ⊙ₗ X)).hom ≫ s ⊴ₗ (t ⊴ₗ 𝟙 _ ≫ (αₗ t A.2 X).inv) ≫
          (αₗ s (t ⊗ A.2) X).inv
      simp only [MonoidalLeftAction.actionHomRight_id, Category.id_comp]
      exact Functor.LaxLeftLinear.μₗ_associativity (MonoidalLeftAction.actionRight C X) s t A.2


/-- The middle pair carries the constructed diagonal-action linear structure. -/
instance switchMiddlePairLinear [IsGroupoid C] (X : D) :
    (switchMiddlePair (C := C) X).LaxLeftLinear C where
  μₗ := switchMiddleLineator X
  μₗ_naturality_left f A := switchMiddleLineator_naturality_left X f A
  μₗ_naturality_right s _ _ f := switchMiddleLineator_naturality_right X s f
  μₗ_associativity s t A := switchMiddleLineator_associativity X s t A
  μₗ_unitality A := switchMiddleLineator_unitality X A

/-- The actual middle functor in the homotopy-commuting switch square. -/
def switchMiddle [IsGroupoid C] (X : D) :
    Localization C C ⥤ Localization C (Localization C D) :=
  ActionLocalization.mapFunctor (switchMiddlePair X)

@[simp]
lemma switchMiddle_obj [IsGroupoid C] (X : D) (A : Localization C C) :
    (switchMiddle X).obj A = ⟨(A.obj.2, ⟨(A.obj.2 ⊗ A.obj.1, A.obj.2 ⊙ₗ X)⟩)⟩ := rfl

/-- The middle functor keeps the original outer denominator and uses it again inside. -/
lemma switchMiddle_mkHom [IsGroupoid C] (X : D) {A B : C × C} (s : C)
    (f : s ⊗ A.1 ⟶ B.1) (g : s ⊗ A.2 ⟶ B.2) :
    (switchMiddle X).map (mkHom s f g) =
      mkHom (X := (A.2, (⟨(A.2 ⊗ A.1, A.2 ⊙ₗ X)⟩ : Localization C D)))
        (Y := (B.2, (⟨(B.2 ⊗ B.1, B.2 ⊙ₗ X)⟩ : Localization C D))) s g
        (mkHom (X := ((A.2 ⊗ A.1) ⊗ s, A.2 ⊙ₗ X))
          (Y := (B.2 ⊗ B.1, B.2 ⊙ₗ X)) s
          (switchMiddleShuffle s A.1 A.2 ≫ (g ⊗ₘ f))
          ((αₗ s A.2 X).inv ≫ g ⊵ₗ X)) := by
  change ActionLocalization.mkHom
    (X := (A.2, (⟨(A.2 ⊗ A.1, A.2 ⊙ₗ X)⟩ : Localization C D)))
    (Y := (B.2, (⟨(B.2 ⊗ B.1, B.2 ⊙ₗ X)⟩ : Localization C D)))
    ⟨s, (𝟙 _ ≫ g, _ ≫ ActionLocalization.ofHom
      (X := ((s ⊗ A.2) ⊗ (s ⊗ A.1), (s ⊗ A.2) ⊙ₗ X))
      (Y := (B.2 ⊗ B.1, B.2 ⊙ₗ X)) (g ⊗ₘ f, g ⊵ₗ X))⟩ = _
  rw [Category.id_comp]
  dsimp only [Functor.LaxLeftLinear.μₗ, switchMiddlePairLinear, switchMiddleLineator]
  unfold mkHom
  rw [ActionLocalization.mkHom_comp_ofHom]
  rfl

end Quillen.GroupCompletion.Localization
