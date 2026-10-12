/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Topology.ClassifyingSpace.IteratedTransitions

/-! # Homotopy equivalences for the prescribed iterated comma transitions -/
noncomputable section
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Quillen Quillen.GroupCompletion Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
  [∀ X : D, (MonoidalLeftAction.actionRight C X).Faithful]
  [∀ (X Y : D) (f : X ⟶ Y), Mono f]
attribute [local instance] firstCoordinateLeftAction

example {X Y : ActionLocalization C D} (f : X ⟶ Y) :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (CostructuredArrow iteratedSecondProjection X))
      (ClassifyingSpace (CostructuredArrow iteratedSecondProjection Y)) :=
  iteratedCommaTransitionHomotopyEquiv f

example {X Y : ActionLocalization C D} (f : X ⟶ Y) :
    (iteratedCommaTransitionHomotopyEquiv f).toFun =
      classifyingSpaceMapUniversal (CostructuredArrow.map
        (S := iteratedSecondProjection (C := C) (D := D)) f) :=
  iteratedCommaTransitionHomotopyEquiv_toFun f

example (X : D) :
    (iteratedCommaEntryClassifyingHomotopyEquiv (C := C) X).toFun =
      classifyingSpaceMapUniversal (iteratedCommaEntry X) :=
  iteratedCommaEntryClassifyingHomotopyEquiv_toFun X
