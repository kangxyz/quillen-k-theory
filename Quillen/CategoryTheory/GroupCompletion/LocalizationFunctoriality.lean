/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.CategoryTheory.GroupCompletion.IteratedFiberEntry
public import Quillen.CategoryTheory.GroupCompletion.UnitEntry

/-! # Equivariant functors on the original localization and its iteration -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u₁ v₁ u₂ v₂
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Functor.LaxLeftLinear
namespace Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalLeftAction C D]
  {E : Type u₂} [Category.{v₂} E] [MonoidalLeftAction C E]
  (F : D ⥤ E) [F.LaxLeftLinear C]

/-- Keep the denominator coordinate and apply the original equivariant functor. -/
def mapPair : C × D ⥤ C × E := (𝟭 C).prod F

instance mapPairLinear : (mapPair (C := C) F).LaxLeftLinear C where
  μₗ s X := (𝟙 _, μₗ F s X.2)
  μₗ_naturality_left f X := by
    apply Prod.ext
    · change (f ▷ X.1) ≫ 𝟙 _ = 𝟙 _ ≫ (f ▷ X.1)
      simp
    · exact μₗ_naturality_left F f X.2
  μₗ_naturality_right s _ _ f := by
    apply Prod.ext
    · change (s ◁ f.1) ≫ 𝟙 _ = 𝟙 _ ≫ (s ◁ f.1)
      simp
    · exact μₗ_naturality_right F s f.2
  μₗ_associativity s t X := by
    apply Prod.ext
    · change 𝟙 _ ≫ (α_ s t X.1).hom = (α_ s t X.1).hom ≫ s ◁ 𝟙 _ ≫ 𝟙 _
      simp
    · exact μₗ_associativity F s t X.2
  μₗ_unitality X := by
    apply Prod.ext
    · change (λ_ X.1).hom = 𝟙 _ ≫ (λ_ X.1).hom
      simp
    · exact μₗ_unitality F X.2

/-- Descent to Grayson's original localization, retaining the original denominator. -/
def map : Localization C D ⥤ Localization C E := ActionLocalization.mapFunctor (mapPair F)

@[simp]
lemma map_obj (X : Localization C D) : (map F).obj X = ⟨(X.obj.1, F.obj X.obj.2)⟩ := rfl

@[simp]
lemma map_mkHom {X Y : C × D} (s : C) (f : s ⊗ X.1 ⟶ Y.1)
    (g : s ⊙ₗ X.2 ⟶ Y.2) :
    (map F).map (mkHom s f g) =
      mkHom (X := (X.1, F.obj X.2)) (Y := (Y.1, F.obj Y.2)) s f
        (μₗ F s X.2 ≫ F.map g) := by
  change ActionLocalization.mkHom (X := (X.1, F.obj X.2))
    (Y := (Y.1, F.obj Y.2)) ⟨s, (𝟙 _ ≫ f, _)⟩ = _
  rw [Category.id_comp]
  rfl

@[simp]
lemma map_ofHom {X Y : C × D} (f : X ⟶ Y) :
    (map F).map (ActionLocalization.ofHom (C := C) f) =
      ActionLocalization.ofHom (C := C) (f.1, F.map f.2) :=
  ActionLocalization.mapFunctor_ofHom (mapPair F) f

@[simp]
lemma map_secondFiberHom (X : D) {A B : C} (f : A ⟶ B) :
    (map F).map (secondFiberHom X f) = secondFiberHom (F.obj X) f := by
  unfold secondFiberHom
  rw [map_ofHom, F.map_id]

/-- The canonical unit entry is strictly natural in the original functor. -/
lemma unitEntry_map : unitEntry (C := C) (D := D) ⋙ map F = F ⋙ unitEntry := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  change (map F).map (ActionLocalization.ofHom (X := (𝟙_ C, X))
    (Y := (𝟙_ C, Y)) (𝟙 _, f)) = 𝟙 _ ≫ ActionLocalization.ofHom
      (X := (𝟙_ C, F.obj X)) (Y := (𝟙_ C, F.obj Y)) (𝟙 _, F.map f) ≫ 𝟙 _
  rw [map_ofHom]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

end Quillen.GroupCompletion.Localization
