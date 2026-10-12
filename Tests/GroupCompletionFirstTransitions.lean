/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Topology.ClassifyingSpace.IteratedFirstTransitions

/-! # Actual iterated first-projection transition inverses -/
noncomputable section
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Quillen Quillen.GroupCompletion Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [IsGroupoid C] [∀ A : C, (tensorRight A).Faithful]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
attribute [local instance] firstCoordinateLeftAction
example {A B : ActionLocalization C C} (f : A ⟶ B) :
    ∃ h : ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (CostructuredArrow (projection (D := Localization C D)) A))
      (ClassifyingSpace (CostructuredArrow (projection (D := Localization C D)) B)),
      h.toFun = classifyingSpaceMapUniversal
        (CostructuredArrow.map (S := projection (D := Localization C D)) f) :=
  exists_iteratedFirstTransitionHomotopyEquiv f
