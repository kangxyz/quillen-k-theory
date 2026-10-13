/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.ClassifyingSpace.GroupCompletionIdempotence

/-! # The canonical second-localization entry is a weak equivalence -/
noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Quillen Quillen.GroupCompletion Quillen.GroupCompletion.Localization
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  [MonoidalCategory C] [SymmetricCategory C] [IsGroupoid C]
  [∀ A : C, (tensorRight A).Faithful] [MonoidalLeftAction C D]
attribute [local instance] firstCoordinateLeftAction
example : IsWeakHomotopyEquivalence
    (classifyingSpaceMap (iteratedUnitEntry (C := C) (D := D))).hom :=
  iteratedUnitEntry_isWeakHomotopyEquivalence
example (X : Localization C D) : iteratedUnitEntry.obj X =
    (⟨(𝟙_ C, X)⟩ : Localization C (Localization C D)) := rfl
