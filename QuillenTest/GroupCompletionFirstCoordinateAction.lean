/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.CategoryTheory.GroupCompletion.SecondProjectionLinear

/-! # Genuine first-coordinate action and the iterated second projection -/
noncomputable section
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Quillen.GroupCompletion Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

example : MonoidalRightAction C (Localization C D) := firstCoordinateRightAction

example (s t : C) : firstCoordinateTranslation (D := D) (s ⊗ t) ≅
    firstCoordinateTranslation s ⋙ firstCoordinateTranslation t :=
  firstCoordinateAssociator s t

variable [BraidedCategory C]
attribute [local instance] firstCoordinateLeftAction

example (s : C) (X : Localization C D) : s ⊙ₗ X = ⟨(X.obj.1 ⊗ s, X.obj.2)⟩ :=
  firstCoordinateLeftAction_obj s X

example : Localization C (Localization C D) ⥤ ActionLocalization C D :=
  iteratedSecondProjection

example {X Y : C × Localization C D} (s : C)
    (f : s ⊗ X.1 ⟶ Y.1) (g : s ⊙ₗ X.2 ⟶ Y.2) :
    iteratedSecondProjection.map (mkHom s f g) = secondProjection.map g :=
  iteratedSecondProjection_mkHom s f g
