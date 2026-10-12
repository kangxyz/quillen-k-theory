/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.GroupCompletion.ActionLocalization

/-!
# Naturality of the original action-localization translation arrows

The common-denominator translation arrows intertwine the original category
maps with the translated maps. This supplies the successor squares for actual
finite-stage maps into the group-completion category.
-/
@[expose] public section

universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction

namespace Quillen.GroupCompletion.ActionLocalization
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [MonoidalCategory C] [MonoidalLeftAction C D]

/-- Translation intertwines a map with its original action translate. -/
@[reassoc]
lemma ofHom_translation (s : C) {X Y : D} (f : X ⟶ Y) :
    ofHom (C := C) f ≫ translation s Y =
      translation s X ≫ ofHom (s ⊴ₗ f) := by
  rw [← mkHom_factorization (⟨s, s ⊴ₗ f⟩ : HomRep X (s ⊙ₗ Y))]
  apply Quotient.sound
  refine ⟨ρ_ s, ?_⟩
  simp [HomRep.comp]

end Quillen.GroupCompletion.ActionLocalization
