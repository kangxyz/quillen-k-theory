/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Assemble a square isomorphism from its four original corner isomorphisms

The ordinary four edge equations suffice. Keeping this construction polymorphic
avoids unfolding concrete diagram values when checking the outer arrow equation.
-/
@[expose] public section
open CategoryTheory
universe u v u₁ v₁
namespace CategoryTheory.Arrow
variable {C : Type u} [Category.{v} C] {S T : Arrow (Arrow C)}

/-- The actual square isomorphism supplied by four corner isomorphisms and four edge laws. -/
def squareIsoMk (e₀ : S.left.left ≅ T.left.left) (e₁ : S.left.right ≅ T.left.right)
    (e₂ : S.right.left ≅ T.right.left) (e₃ : S.right.right ≅ T.right.right)
    (h₀ : e₀.hom ≫ T.left.hom = S.left.hom ≫ e₁.hom)
    (h₁ : e₀.hom ≫ T.hom.left = S.hom.left ≫ e₂.hom)
    (h₂ : e₁.hom ≫ T.hom.right = S.hom.right ≫ e₃.hom)
    (h₃ : e₂.hom ≫ T.right.hom = S.right.hom ≫ e₃.hom) : S ≅ T :=
  Arrow.isoMk (Arrow.isoMk e₀ e₁ h₀) (Arrow.isoMk e₂ e₃ h₃) (by
    apply Arrow.hom_ext
    · exact h₁
    · exact h₂)

/-- Assemble a square map against the literal functor image from the four original edges. -/
def squareMapHomMk {D : Type u₁} [Category.{v₁} D] (B : C ⥤ D)
    (S : Arrow (Arrow C)) (T : Arrow (Arrow D))
    (e₀ : T.left.left ⟶ B.obj S.left.left)
    (e₁ : T.left.right ⟶ B.obj S.left.right)
    (e₂ : T.right.left ⟶ B.obj S.right.left)
    (e₃ : T.right.right ⟶ B.obj S.right.right)
    (h₀ : e₀ ≫ B.map S.left.hom = T.left.hom ≫ e₁)
    (h₁ : e₀ ≫ B.map S.hom.left = T.hom.left ≫ e₂)
    (h₂ : e₁ ≫ B.map S.hom.right = T.hom.right ≫ e₃)
    (h₃ : e₂ ≫ B.map S.right.hom = T.right.hom ≫ e₃) :
    T ⟶ B.mapArrow.mapArrow.obj S :=
  Arrow.homMk (Arrow.homMk e₀ e₁ h₀) (Arrow.homMk e₂ e₃ h₃) (by
    apply Arrow.hom_ext
    · exact h₁
    · exact h₂)

section Components
variable {D : Type u₁} [Category.{v₁} D] (B : C ⥤ D)
    (S : Arrow (Arrow C)) (T : Arrow (Arrow D))
    (e₀ : T.left.left ⟶ B.obj S.left.left)
    (e₁ : T.left.right ⟶ B.obj S.left.right)
    (e₂ : T.right.left ⟶ B.obj S.right.left)
    (e₃ : T.right.right ⟶ B.obj S.right.right)
    (h₀ : e₀ ≫ B.map S.left.hom = T.left.hom ≫ e₁)
    (h₁ : e₀ ≫ B.map S.hom.left = T.hom.left ≫ e₂)
    (h₂ : e₁ ≫ B.map S.hom.right = T.hom.right ≫ e₃)
    (h₃ : e₂ ≫ B.map S.right.hom = T.right.hom ≫ e₃)

/-- The source component of the assembled map is the specified source map. -/
theorem squareMapHomMk_left_left :
    (squareMapHomMk B S T e₀ e₁ e₂ e₃ h₀ h₁ h₂ h₃).left.left = e₀ := rfl

/-- The upper component of the assembled map is the specified upper map. -/
theorem squareMapHomMk_left_right :
    (squareMapHomMk B S T e₀ e₁ e₂ e₃ h₀ h₁ h₂ h₃).left.right = e₁ := rfl

/-- The lower component of the assembled map is the specified lower map. -/
theorem squareMapHomMk_right_left :
    (squareMapHomMk B S T e₀ e₁ e₂ e₃ h₀ h₁ h₂ h₃).right.left = e₂ := rfl

/-- The terminal component of the assembled map is the specified terminal map. -/
theorem squareMapHomMk_right_right :
    (squareMapHomMk B S T e₀ e₁ e₂ e₃ h₀ h₁ h₂ h₃).right.right = e₃ := rfl
end Components

end CategoryTheory.Arrow
