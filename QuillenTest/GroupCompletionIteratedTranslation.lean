/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.ClassifyingSpace.IteratedTranslation
import Quillen.Topology.HomotopyEquiv.HomotopySquare

/-! # Actual translation squares, including the prescribed topological map -/
noncomputable section
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Quillen.GroupCompletion Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
attribute [local instance] firstCoordinateLeftAction

example {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y) :
    iteratedCommaEntry X ⋙ CostructuredArrow.map (ActionLocalization.mkHom ⟨s, g⟩) ⟶
      secondTranslation s ⋙ iteratedCommaEntry Y :=
  iteratedCommaTranslation s g

example [∀ X : D, (MonoidalLeftAction.actionRight C X).Faithful]
    [∀ (X Y : D) (f : X ⟶ Y), Mono f]
    {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y) (A B : C) :
    iteratedSecondProjection.IsStronglyCocartesian
      (iteratedSecondProjection.map (iteratedRightLift s g A B))
      (iteratedRightLift s g A B) := inferInstance

example {X Y X' Y' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    (a : ContinuousMap.HomotopyEquiv X X') (b : ContinuousMap.HomotopyEquiv Y Y')
    (t : ContinuousMap.HomotopyEquiv X Y) (f : C(X', Y'))
    (h : (f.comp a.toFun).Homotopic (b.toFun.comp t.toFun)) :
    (ContinuousMap.HomotopyEquiv.ofHomotopySquare a b t f h).toFun = f := rfl

example {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y) :
    Nonempty (((Quillen.classifyingSpaceMapUniversal (CostructuredArrow.map
      (S := iteratedSecondProjection (C := C) (D := D))
      (ActionLocalization.mkHom ⟨s, g⟩))).comp
        (Quillen.classifyingSpaceMapUniversal (iteratedCommaEntry X))).Homotopy
      ((Quillen.classifyingSpaceMapUniversal (iteratedCommaEntry Y)).comp
        (translationClassifyingHomotopyEquiv s).symm.toFun)) :=
  ⟨iteratedCommaTranslationHomotopy s g⟩
