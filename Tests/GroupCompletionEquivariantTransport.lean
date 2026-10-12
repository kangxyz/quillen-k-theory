/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Topology.ClassifyingSpace.EquivariantTransport

/-! # Actual equivariant transport across weakly contractible action categories -/
noncomputable section
universe u v u₁ v₁ u₂ v₂ w₁ w₂
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Quillen Quillen.GroupCompletion Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [IsGroupoid C] [∀ A : C, (tensorRight A).Faithful]
  {D : Type u₁} [Category.{v₁} D] [MonoidalLeftAction C D]
  [∀ X : D, (MonoidalLeftAction.actionRight C X).Faithful]
  [∀ (X Y : D) (f : X ⟶ Y), Mono f]
  {E : Type u₂} [Category.{v₂} E] [MonoidalLeftAction C E]
  [∀ X : E, (MonoidalLeftAction.actionRight C X).Faithful]
  [∀ (X Y : E) (f : X ⟶ Y), Mono f]
  (F : D ⥤ E) [F.LaxLeftLinear C]
attribute [local instance] firstCoordinateLeftAction

example (X : D) :
    iteratedFiberEntry X ⋙ iteratedMap (C := C) F = iteratedFiberEntry (F.obj X) :=
  iteratedFiberEntry_map F X

example : unitEntry (C := C) (D := Localization C D) ⋙ iteratedMap F =
    map F ⋙ unitEntry := iteratedMap_unitEntry F

example (X : D)
    (hD : IsWeakHomotopyEquivalence (ContinuousMap.const
      (ClassifyingSpace (ActionLocalization C D)) (PUnit.unit : PUnit.{w₁ + 1})))
    (hE : IsWeakHomotopyEquivalence (ContinuousMap.const
      (ClassifyingSpace (ActionLocalization C E)) (PUnit.unit : PUnit.{w₂ + 1}))) :
    IsWeakHomotopyEquivalence (classifyingSpaceMapUniversal (map (C := C) F)) :=
  map_isWeakHomotopyEquivalence_of_weakBases F X hD hE
