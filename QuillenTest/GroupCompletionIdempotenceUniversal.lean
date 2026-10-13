/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.ClassifyingSpace.GroupCompletionIdempotenceUniversal

/-! # Independent-universe consumers of the original iterated unit entry -/
@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory Quillen Quillen.GroupCompletion
open scoped MonoidalLeftAction
universe u v u' v'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [IsGroupoid C] [∀ A : C, (tensorRight A).Faithful]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
attribute [local instance] Localization.firstCoordinateLeftAction

example : IsWeakHomotopyEquivalence
    (classifyingSpaceMapUniversal (Localization.unitEntry (C := C) (D := Localization C D))) :=
  Localization.unitEntry_iterated_isWeakHomotopyEquivalence

example (X : Localization C D) :
    (Localization.unitEntry (C := C) (D := Localization C D)).obj X =
      (⟨(𝟙_ C, X)⟩ : Localization C (Localization C D)) := rfl
