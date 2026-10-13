/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.CategoryTheory.Monoidal.Action.Orbit
public import Quillen.CategoryTheory.GroupCompletion.DiagonalAction
public import Quillen.CategoryTheory.GroupCompletion.Functoriality

/-! # The original orbit entry into action localization -/
@[expose] public section
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

/-- Keep the first coordinate and apply the orbit functor to the second. -/
def orbitPair (X : D) : C × C ⥤ C × D := (𝟭 C).prod (MonoidalLeftAction.actionRight C X)

/-- The orbit pair inherits the diagonal action linear structure. -/
instance orbitPairLinear (X : D) : (orbitPair (C := C) X).LaxLeftLinear C where
  μₗ s A := (𝟙 _, (αₗ s A.2 X).inv)
  μₗ_naturality_left f A := by
    apply Prod.ext
    · change (f ▷ A.1) ≫ 𝟙 _ = 𝟙 _ ≫ (f ▷ A.1)
      simp
    · exact Functor.LaxLeftLinear.μₗ_naturality_left (MonoidalLeftAction.actionRight C X) f A.2
  μₗ_naturality_right s _ _ f := by
    apply Prod.ext
    · change (s ◁ f.1) ≫ 𝟙 _ = 𝟙 _ ≫ (s ◁ f.1)
      simp
    · exact Functor.LaxLeftLinear.μₗ_naturality_right (MonoidalLeftAction.actionRight C X) s f.2
  μₗ_associativity s t A := by
    apply Prod.ext
    · change 𝟙 _ ≫ (α_ s t A.1).hom = (α_ s t A.1).hom ≫ s ◁ 𝟙 _ ≫ 𝟙 _
      simp
    · exact Functor.LaxLeftLinear.μₗ_associativity (MonoidalLeftAction.actionRight C X) s t A.2
  μₗ_unitality A := by
    apply Prod.ext
    · change (λ_ A.1).hom = 𝟙 _ ≫ (λ_ A.1).hom
      simp
    · exact Functor.LaxLeftLinear.μₗ_unitality (MonoidalLeftAction.actionRight C X) A.2

/-- Grayson's canonical map `(A,B) ↦ (A,B ⊙ X)`, with its actual quotient action. -/
def orbitEntry (X : D) : Localization C C ⥤ Localization C D :=
  ActionLocalization.mapFunctor (orbitPair X)

@[simp]
lemma orbitEntry_obj (X : D) (A : Localization C C) :
    (orbitEntry X).obj A = ⟨(A.obj.1, A.obj.2 ⊙ₗ X)⟩ := rfl

@[simp]
lemma orbitEntry_mkHom (X : D) {A B : C × C} (s : C)
    (f : s ⊗ A.1 ⟶ B.1) (g : s ⊗ A.2 ⟶ B.2) :
    (orbitEntry X).map (mkHom s f g) =
      mkHom (X := (A.1, A.2 ⊙ₗ X)) (Y := (B.1, B.2 ⊙ₗ X))
        s f ((αₗ s A.2 X).inv ≫ g ⊵ₗ X) := by
  change ActionLocalization.mkHom (X := (A.1, A.2 ⊙ₗ X))
    (Y := (B.1, B.2 ⊙ₗ X)) ⟨s, (𝟙 _ ≫ f, _)⟩ = _
  rw [Category.id_comp]
  rfl

end Quillen.GroupCompletion.Localization
