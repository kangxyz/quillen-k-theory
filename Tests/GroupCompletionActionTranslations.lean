/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Topology.ClassifyingSpace.ActionTranslations

/-! # Actual translation inverses for arbitrary acted-on categories -/
noncomputable section
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Quillen Quillen.GroupCompletion Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

example (s : C) : (MonoidalLeftAction.actionLeft D s).LaxLeftLinear C := inferInstance

example (s : C) : 𝟭 (Localization C D) ⟶
    firstCoordinateTranslation s ⋙ secondActionTranslation s := actionDiagonalTranslation s

example (s : C) :
    (actionTranslationClassifyingHomotopyEquiv (D := D) s).toFun =
      classifyingSpaceMapUniversal (firstCoordinateTranslation s) := rfl

example (s : C) :
    (actionTranslationClassifyingHomotopyEquiv (D := D) s).invFun =
      classifyingSpaceMapUniversal (secondActionTranslation s) := rfl
