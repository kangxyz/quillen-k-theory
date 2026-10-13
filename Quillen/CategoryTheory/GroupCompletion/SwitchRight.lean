/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.CategoryTheory.GroupCompletion.SwitchMiddleLinear

/-! # The right natural arrow in Grayson's switch comparison -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalLeftAction
namespace Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [IsGroupoid C] {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
attribute [local instance] firstCoordinateLeftAction

/-- The switched fiber entry before action localization. -/
def switchRightPair (X : D) : C × C ⥤ C × Localization C D :=
  CategoryTheory.Prod.swap C C ⋙ fixedSecondPairEntry X

instance switchRightPairLinear (X : D) : (switchRightPair (C := C) X).LaxLeftLinear C where
  μₗ s A := (𝟙 _, secondFiberHom X (β_ A.1 s).hom)
  μₗ_naturality_left f A := by
    apply Prod.ext
    · change (f ▷ A.2) ≫ 𝟙 _ = 𝟙 _ ≫ (f ▷ A.2)
      simp
    · exact Functor.LaxLeftLinear.μₗ_naturality_left (fixedSecondEntry X) f A.1
  μₗ_naturality_right s _ _ f := by
    apply Prod.ext
    · change (s ◁ f.2) ≫ 𝟙 _ = 𝟙 _ ≫ (s ◁ f.2)
      simp
    · exact Functor.LaxLeftLinear.μₗ_naturality_right (fixedSecondEntry X) s f.1
  μₗ_associativity s t A := by
    apply Prod.ext
    · change 𝟙 _ ≫ (α_ s t A.2).hom = (α_ s t A.2).hom ≫ s ◁ 𝟙 _ ≫ 𝟙 _
      simp
    · exact Functor.LaxLeftLinear.μₗ_associativity (fixedSecondEntry X) s t A.1
  μₗ_unitality A := by
    apply Prod.ext
    · change (λ_ A.2).hom = 𝟙 _ ≫ (λ_ A.2).hom
      simp
    · exact Functor.LaxLeftLinear.μₗ_unitality (fixedSecondEntry X) A.1

/-- Simultaneously translate the inner coordinates by the displayed second actor. -/
def switchRightPairToMiddle (X : D) : switchRightPair (C := C) X ⟶ switchMiddlePair X where
  app A := (𝟙 A.2, mkHom (X := (A.1, X)) (Y := (A.2 ⊗ A.1, A.2 ⊙ₗ X))
    A.2 (𝟙 _) (𝟙 _))
  naturality {A B} f := by
    apply Prod.ext
    · change f.2 ≫ 𝟙 _ = 𝟙 _ ≫ f.2
      simp
    · change secondFiberHom X f.1 ≫
        mkHom (X := (B.1, X)) (Y := (B.2 ⊗ B.1, B.2 ⊙ₗ X)) B.2 (𝟙 _) (𝟙 _) =
        mkHom (X := (A.1, X)) (Y := (A.2 ⊗ A.1, A.2 ⊙ₗ X)) A.2 (𝟙 _) (𝟙 _) ≫
          ActionLocalization.ofHom (X := (A.2 ⊗ A.1, A.2 ⊙ₗ X))
            (Y := (B.2 ⊗ B.1, B.2 ⊙ₗ X)) (f.2 ⊗ₘ f.1, f.2 ⊵ₗ X)
      unfold secondFiberHom mkHom
      rw [ActionLocalization.ofHom_comp_mkHom, ActionLocalization.mkHom_comp_ofHom]
      symm
      apply Quotient.sound
      refine ⟨asIso f.2, ?_⟩
      apply Prod.ext
      · change f.2 ▷ A.1 ≫ (B.2 ◁ f.1 ≫ 𝟙 _) = 𝟙 _ ≫ (f.2 ⊗ₘ f.1)
        simp only [Category.comp_id, Category.id_comp, tensorHom_def]
      · change f.2 ⊵ₗ X ≫ (B.2 ⊴ₗ 𝟙 X ≫ 𝟙 _) = 𝟙 _ ≫ f.2 ⊵ₗ X
        simp

/-- The right middle arrow respects the genuine lineators. -/
lemma switchRightPairToMiddle_linear (X : D) (s : C) (A : C × C) :
    Functor.LaxLeftLinear.μₗ (switchRightPair X) s A ≫
        (switchRightPairToMiddle X).app (s ⊙ₗ A) =
      s ⊴ₗ (switchRightPairToMiddle X).app A ≫
        Functor.LaxLeftLinear.μₗ (switchMiddlePair X) s A := by
  apply Prod.ext
  · change 𝟙 _ ≫ 𝟙 _ = s ◁ 𝟙 _ ≫ 𝟙 _
    simp
  · change secondFiberHom X (β_ A.1 s).hom ≫
      mkHom (X := (s ⊗ A.1, X))
        (Y := ((s ⊗ A.2) ⊗ (s ⊗ A.1), (s ⊗ A.2) ⊙ₗ X)) (s ⊗ A.2) (𝟙 _) (𝟙 _) =
      (firstCoordinateTranslation s).map
        (mkHom (X := (A.1, X)) (Y := (A.2 ⊗ A.1, A.2 ⊙ₗ X)) A.2 (𝟙 _) (𝟙 _)) ≫
      mkHom (X := ((A.2 ⊗ A.1) ⊗ s, A.2 ⊙ₗ X))
        (Y := ((s ⊗ A.2) ⊗ (s ⊗ A.1), (s ⊗ A.2) ⊙ₗ X)) s
          (switchMiddleShuffle s A.1 A.2) (αₗ s A.2 X).inv
    rw [firstCoordinateTranslation_mkHom]
    unfold secondFiberHom mkHom
    rw [ActionLocalization.ofHom_comp_mkHom]
    change ActionLocalization.mkHom _ =
      ActionLocalization.mkHom (ActionLocalization.HomRep.comp _ _)
    apply congrArg ActionLocalization.mkHom
    apply congrArg (ActionLocalization.HomRep.mk (s ⊗ A.2))
    apply Prod.ext
    · change (s ⊗ A.2) ◁ (β_ A.1 s).hom ≫ 𝟙 _ =
        (α_ s A.2 (A.1 ⊗ s)).hom ≫
          s ◁ ((α_ A.2 A.1 s).inv ≫ 𝟙 _ ▷ s) ≫ switchMiddleShuffle s A.1 A.2
      simp only [id_whiskerRight, Category.comp_id]
      dsimp only [switchMiddleShuffle]
      monoidal
    · change (s ⊗ A.2) ⊴ₗ 𝟙 X ≫ 𝟙 _ =
        (αₗ s A.2 X).hom ≫ s ⊴ₗ 𝟙 _ ≫ (αₗ s A.2 X).inv
      simp

/-- The descended right arrow into the original middle functor. -/
def switchRightToMiddle (X : D) :
    ActionLocalization.mapFunctor (switchRightPair (C := C) X) ⟶ switchMiddle X :=
  ActionLocalization.mapNatTrans (switchRightPair X) (switchRightPairToMiddle X)
    (switchRightPairToMiddle_linear X)

omit [IsGroupoid C] in
/-- The descended right source is exactly the switched original fiber entry. -/
lemma switchRightLocalized_eq (X : D) :
    ActionLocalization.mapFunctor (switchRightPair (C := C) X) =
      switch ⋙ iteratedFiberEntry X := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro A B f
  change _ = 𝟙 _ ≫ (iteratedFiberEntry X).map (switch.map f) ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective A.obj B.obj f
  change _ = (iteratedFiberEntry X).map (switch.map (mkHom r.denom r.map.1 r.map.2))
  rw [switch_mkHom]
  erw [iteratedFiberEntry_mkHom]

/-- The canonical switched fiber entry maps naturally to the genuine middle functor. -/
def switchedFiberToMiddle (X : D) : switch ⋙ iteratedFiberEntry (C := C) X ⟶ switchMiddle X := by
  rw [← switchRightLocalized_eq]
  exact switchRightToMiddle X

end Quillen.GroupCompletion.Localization
