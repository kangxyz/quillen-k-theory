/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Mathlib.CategoryTheory.Monoidal.Action.LinearFunctor

/-! # The canonical linear structure on an orbit functor -/
@[expose] public section
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.MonoidalCategory.MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

/-- Associativity makes the orbit through a fixed object a linear functor. -/
instance actionRightLinear (X : D) : (actionRight C X).LaxLeftLinear C where
  μₗ s t := (αₗ s t X).inv
  μₗ_naturality_left f t := by
    change f ⊵ₗ (t ⊙ₗ X) ≫ (αₗ _ t X).inv = (αₗ _ t X).inv ≫ (f ▷ t) ⊵ₗ X
    simp only [whiskerRight_actionHomLeft, Iso.inv_hom_id_assoc]
  μₗ_naturality_right s _ _ f := by
    change s ⊴ₗ (f ⊵ₗ X) ≫ (αₗ s _ X).inv = (αₗ s _ X).inv ≫ (s ◁ f) ⊵ₗ X
    simp only [whiskerLeft_actionHomLeft, Iso.inv_hom_id_assoc]
  μₗ_associativity s t r := by
    change (αₗ (s ⊗ t) r X).inv ≫ (α_ s t r).hom ⊵ₗ X =
      (αₗ s t (r ⊙ₗ X)).hom ≫ s ⊴ₗ (αₗ t r X).inv ≫ (αₗ s (t ⊗ r) X).inv
    apply (cancel_mono ((αₗ s (t ⊗ r) X).hom ≫ s ⊴ₗ (αₗ t r X).hom)).1
    simp only [Category.assoc, associator_actionHom, Iso.inv_hom_id_assoc,
      ← actionHomRight_comp, Iso.inv_hom_id, actionHomRight_id, Category.comp_id]
  μₗ_unitality t := by
    change (λₗ (t ⊙ₗ X)).hom = (αₗ (𝟙_ C) t X).inv ≫ (λ_ t).hom ⊵ₗ X
    simp only [leftUnitor_actionHom, Iso.inv_hom_id_assoc]

end CategoryTheory.MonoidalCategory.MonoidalLeftAction
