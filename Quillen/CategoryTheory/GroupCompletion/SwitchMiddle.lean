/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.CategoryTheory.GroupCompletion.IteratedFiberEntry
public import Quillen.CategoryTheory.GroupCompletion.OrbitEntry
public import Quillen.CategoryTheory.GroupCompletion.Switch

/-! # The middle functor in Grayson's switch comparison -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalLeftAction
namespace Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

/-- The middle object before localization, with its genuine functorial action
on the two actor coordinates. -/
def switchMiddlePair (X : D) : C × C ⥤ C × Localization C D where
  obj A := (A.2, ⟨(A.2 ⊗ A.1, A.2 ⊙ₗ X)⟩)
  map {A B} f := (f.2, ActionLocalization.ofHom
    (X := (A.2 ⊗ A.1, A.2 ⊙ₗ X)) (Y := (B.2 ⊗ B.1, B.2 ⊙ₗ X))
      (f.2 ⊗ₘ f.1, f.2 ⊵ₗ X))
  map_id A := by
    apply Prod.ext
    · rfl
    · change ActionLocalization.ofHom (X := (A.2 ⊗ A.1, A.2 ⊙ₗ X))
        (Y := (A.2 ⊗ A.1, A.2 ⊙ₗ X)) (𝟙 _ ⊗ₘ 𝟙 _, 𝟙 A.2 ⊵ₗ X) = 𝟙 _
      rw [tensorHom_id, id_whiskerRight, MonoidalLeftAction.id_actionHomLeft]
      exact ActionLocalization.ofHom_id (C := C) (A.2 ⊗ A.1, A.2 ⊙ₗ X)
  map_comp {A B T} f g := by
    apply Prod.ext
    · rfl
    · change ActionLocalization.ofHom
        (X := (A.2 ⊗ A.1, A.2 ⊙ₗ X)) (Y := (T.2 ⊗ T.1, T.2 ⊙ₗ X))
        ((f.2 ≫ g.2) ⊗ₘ (f.1 ≫ g.1), (f.2 ≫ g.2) ⊵ₗ X) = _
      dsimp only [CategoryTheory.prod_comp]
      rw [← ActionLocalization.ofHom_comp]
      congr 1
      exact Prod.ext (tensorHom_comp_tensorHom _ _ _ _).symm
        (MonoidalLeftAction.comp_actionHomLeft _ _ _)

variable [BraidedCategory C]
attribute [local instance] firstCoordinateLeftAction

/-- Reorder the two copies of the translating object in the middle lineator. -/
def switchMiddleShuffle (s A B : C) : s ⊗ ((B ⊗ A) ⊗ s) ⟶ (s ⊗ B) ⊗ (s ⊗ A) :=
  (α_ s (B ⊗ A) s).inv ≫ (α_ s B A).inv ▷ s ≫
    (α_ (s ⊗ B) A s).hom ≫ (s ⊗ B) ◁ (β_ A s).hom

/-- The structural shuffle is natural in both source coordinates. -/
lemma switchMiddleShuffle_naturality (s : C) {A A' B B' : C}
    (f : A ⟶ A') (g : B ⟶ B') :
    s ◁ ((g ⊗ₘ f) ▷ s) ≫ switchMiddleShuffle s A' B' =
      switchMiddleShuffle s A B ≫ ((s ◁ g) ⊗ₘ (s ◁ f)) := by
  dsimp only [switchMiddleShuffle]
  simp only [← id_tensorHom, ← tensorHom_id, Category.assoc]
  rw [associator_inv_naturality_assoc]
  rw [tensorHom_comp_tensorHom_assoc, associator_inv_naturality]
  simp only [Category.id_comp, tensorHom_id, comp_whiskerRight, Category.assoc]
  simp only [← tensorHom_id]
  rw [associator_naturality_assoc]
  rw [tensorHom_comp_tensorHom, braiding_naturality]
  simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

/-- The same structural shuffle is natural when the translating object varies. -/
lemma switchMiddleShuffle_naturality_actor {s t : C} (f : s ⟶ t) (A B : C) :
    (f ⊗ₘ (𝟙 (B ⊗ A) ⊗ₘ f)) ≫ switchMiddleShuffle t A B =
      switchMiddleShuffle s A B ≫ ((f ▷ B) ⊗ₘ (f ▷ A)) := by
  have h₂ : ((f ⊗ₘ 𝟙 (B ⊗ A)) ⊗ₘ f) ≫ ((α_ t B A).inv ▷ t) =
      ((α_ s B A).inv ▷ s) ≫ (((f ▷ B) ▷ A) ⊗ₘ f) := by
    simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    rw [← id_tensorHom_id B A, associator_inv_naturality]
  have h₄ : (((f ▷ B) ⊗ₘ (𝟙 A ⊗ₘ f))) ≫ ((t ⊗ B) ◁ (β_ A t).hom) =
      ((s ⊗ B) ◁ (β_ A s).hom) ≫ ((f ▷ B) ⊗ₘ (f ▷ A)) := by
    simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp]
    rw [braiding_naturality]
  dsimp only [switchMiddleShuffle]
  rw [associator_inv_naturality_assoc, reassoc_of% h₂]
  simp only [← tensorHom_id] at ⊢ h₄
  rw [associator_naturality_assoc, h₄]
  simp only [Category.assoc]

/-- The middle lineator uses one additional common denominator. -/
def switchMiddleLineator (X : D) (s : C) (A : C × C) :
    s ⊙ₗ (switchMiddlePair X).obj A ⟶ (switchMiddlePair X).obj (s ⊙ₗ A) :=
  (𝟙 _, mkHom (X := ((A.2 ⊗ A.1) ⊗ s, A.2 ⊙ₗ X))
    (Y := ((s ⊗ A.2) ⊗ (s ⊗ A.1), (s ⊗ A.2) ⊙ₗ X)) s
      (switchMiddleShuffle s A.1 A.2) (αₗ s A.2 X).inv)

/-- The middle lineator respects the two genuine actor-coordinate morphisms. -/
lemma switchMiddleLineator_naturality_right (X : D) (s : C) {A B : C × C} (f : A ⟶ B) :
    s ⊴ₗ (switchMiddlePair X).map f ≫ switchMiddleLineator X s B =
      switchMiddleLineator X s A ≫ (switchMiddlePair X).map (s ⊴ₗ f) := by
  apply Prod.ext
  · change (s ◁ f.2) ≫ 𝟙 _ = 𝟙 _ ≫ (s ◁ f.2)
    simp
  · change (firstCoordinateTranslation s).map
        (ActionLocalization.ofHom (X := (A.2 ⊗ A.1, A.2 ⊙ₗ X))
          (Y := (B.2 ⊗ B.1, B.2 ⊙ₗ X)) (f.2 ⊗ₘ f.1, f.2 ⊵ₗ X)) ≫
      mkHom (X := ((B.2 ⊗ B.1) ⊗ s, B.2 ⊙ₗ X))
        (Y := ((s ⊗ B.2) ⊗ (s ⊗ B.1), (s ⊗ B.2) ⊙ₗ X)) s
          (switchMiddleShuffle s B.1 B.2) (αₗ s B.2 X).inv =
      mkHom (X := ((A.2 ⊗ A.1) ⊗ s, A.2 ⊙ₗ X))
        (Y := ((s ⊗ A.2) ⊗ (s ⊗ A.1), (s ⊗ A.2) ⊙ₗ X)) s
          (switchMiddleShuffle s A.1 A.2) (αₗ s A.2 X).inv ≫
        ActionLocalization.ofHom
          (X := ((s ⊗ A.2) ⊗ (s ⊗ A.1), (s ⊗ A.2) ⊙ₗ X))
          (Y := ((s ⊗ B.2) ⊗ (s ⊗ B.1), (s ⊗ B.2) ⊙ₗ X))
          ((s ◁ f.2) ⊗ₘ (s ◁ f.1), (s ◁ f.2) ⊵ₗ X)
    unfold firstCoordinateTranslation
    erw [ActionLocalization.mapFunctor_ofHom]
    unfold mkHom
    rw [ActionLocalization.ofHom_comp_mkHom, ActionLocalization.mkHom_comp_ofHom]
    congr 1
    congr 1
    apply Prod.ext
    · exact switchMiddleShuffle_naturality s f.1 f.2
    · change s ⊴ₗ (f.2 ⊵ₗ X) ≫ (αₗ s B.2 X).inv =
        (αₗ s A.2 X).inv ≫ (s ◁ f.2) ⊵ₗ X
      simp only [MonoidalLeftAction.whiskerLeft_actionHomLeft, Iso.inv_hom_id_assoc]

/-- Groupoid actor arrows identify the changing middle denominators. -/
lemma switchMiddleLineator_naturality_left [IsGroupoid C] (X : D)
    {s t : C} (f : s ⟶ t) (A : C × C) :
    f ⊵ₗ (switchMiddlePair X).obj A ≫ switchMiddleLineator X t A =
      switchMiddleLineator X s A ≫ (switchMiddlePair X).map (f ⊵ₗ A) := by
  apply Prod.ext
  · change (f ▷ A.2) ≫ 𝟙 _ = 𝟙 _ ≫ (f ▷ A.2)
    simp
  · change secondFiberHom (A.2 ⊙ₗ X) ((A.2 ⊗ A.1) ◁ f) ≫
      mkHom (X := ((A.2 ⊗ A.1) ⊗ t, A.2 ⊙ₗ X))
        (Y := ((t ⊗ A.2) ⊗ (t ⊗ A.1), (t ⊗ A.2) ⊙ₗ X)) t
          (switchMiddleShuffle t A.1 A.2) (αₗ t A.2 X).inv =
      mkHom (X := ((A.2 ⊗ A.1) ⊗ s, A.2 ⊙ₗ X))
        (Y := ((s ⊗ A.2) ⊗ (s ⊗ A.1), (s ⊗ A.2) ⊙ₗ X)) s
          (switchMiddleShuffle s A.1 A.2) (αₗ s A.2 X).inv ≫
        ActionLocalization.ofHom
          (X := ((s ⊗ A.2) ⊗ (s ⊗ A.1), (s ⊗ A.2) ⊙ₗ X))
          (Y := ((t ⊗ A.2) ⊗ (t ⊗ A.1), (t ⊗ A.2) ⊙ₗ X))
          ((f ▷ A.2) ⊗ₘ (f ▷ A.1), (f ▷ A.2) ⊵ₗ X)
    unfold secondFiberHom mkHom
    rw [ActionLocalization.ofHom_comp_mkHom, ActionLocalization.mkHom_comp_ofHom]
    symm
    apply Quotient.sound
    refine ⟨asIso f, ?_⟩
    apply Prod.ext
    · change f ▷ ((A.2 ⊗ A.1) ⊗ s) ≫
        (t ◁ ((A.2 ⊗ A.1) ◁ f) ≫ switchMiddleShuffle t A.1 A.2) =
          switchMiddleShuffle s A.1 A.2 ≫ ((f ▷ A.2) ⊗ₘ (f ▷ A.1))
      rw [← Category.assoc, ← tensorHom_def, ← id_tensorHom]
      exact switchMiddleShuffle_naturality_actor f A.1 A.2
    · change f ⊵ₗ (A.2 ⊙ₗ X) ≫ (t ⊴ₗ 𝟙 _ ≫ (αₗ t A.2 X).inv) =
        (αₗ s A.2 X).inv ≫ (f ▷ A.2) ⊵ₗ X
      simp only [MonoidalLeftAction.actionHomRight_id, Category.id_comp,
        MonoidalLeftAction.whiskerRight_actionHomLeft, Iso.inv_hom_id_assoc]


/-- At the monoidal unit the middle shuffle is the canonical unit map. -/
lemma switchMiddleShuffle_unit (A B : C) :
    (λ_ ((B ⊗ A) ⊗ (𝟙_ C))).hom ≫ (ρ_ (B ⊗ A)).hom =
      switchMiddleShuffle (𝟙_ C) A B ≫ ((λ_ B).hom ⊗ₘ (λ_ A).hom) := by
  dsimp only [switchMiddleShuffle]
  rw [braiding_tensorUnit_right]
  monoidal

/-- The middle lineator respects the genuine action unitor. -/
lemma switchMiddleLineator_unitality (X : D) (A : C × C) :
    (λₗ ((switchMiddlePair X).obj A)).hom =
      switchMiddleLineator X (𝟙_ C) A ≫ (switchMiddlePair X).map (λₗ A).hom := by
  apply Prod.ext
  · change (λ_ A.2).hom = 𝟙 _ ≫ (λ_ A.2).hom
    simp
  · change (secondFiberHom (A.2 ⊙ₗ X) ((A.2 ⊗ A.1) ◁ 𝟙 (𝟙_ C)) ≫
      secondFiberHom (A.2 ⊙ₗ X) (ρ_ (A.2 ⊗ A.1)).hom) =
      mkHom (X := ((A.2 ⊗ A.1) ⊗ (𝟙_ C), A.2 ⊙ₗ X))
        (Y := (((𝟙_ C) ⊗ A.2) ⊗ ((𝟙_ C) ⊗ A.1), ((𝟙_ C) ⊗ A.2) ⊙ₗ X))
        (𝟙_ C) (switchMiddleShuffle (𝟙_ C) A.1 A.2) (αₗ (𝟙_ C) A.2 X).inv ≫
      ActionLocalization.ofHom
        (X := (((𝟙_ C) ⊗ A.2) ⊗ ((𝟙_ C) ⊗ A.1), ((𝟙_ C) ⊗ A.2) ⊙ₗ X))
        (Y := (A.2 ⊗ A.1, A.2 ⊙ₗ X))
        ((λ_ A.2).hom ⊗ₘ (λ_ A.1).hom, (λ_ A.2).hom ⊵ₗ X)
    rw [secondFiberHom_comp, whiskerLeft_id, Category.id_comp]
    unfold secondFiberHom mkHom
    rw [ActionLocalization.mkHom_comp_ofHom]
    apply congrArg ActionLocalization.mkHom
    apply congrArg (ActionLocalization.HomRep.mk (𝟙_ C))
    apply Prod.ext
    · exact switchMiddleShuffle_unit A.1 A.2
    · change (λₗ (A.2 ⊙ₗ X)).hom ≫ 𝟙 _ =
        (αₗ (𝟙_ C) A.2 X).inv ≫ (λ_ A.2).hom ⊵ₗ X
      simp only [Category.comp_id, MonoidalLeftAction.leftUnitor_actionHom,
        Iso.inv_hom_id_assoc]

end Quillen.GroupCompletion.Localization
