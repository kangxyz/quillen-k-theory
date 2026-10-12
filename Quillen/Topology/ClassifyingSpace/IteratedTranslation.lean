/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.CategoryTheory.GroupCompletion.IteratedComma
public import Quillen.Topology.ClassifyingSpace.UniverseHomotopy
public import Quillen.Topology.ClassifyingSpace.GroupCompletionTranslation
public import Quillen.Topology.HomotopyEquiv.HomotopySquare

/-! # The actual realized transport square for the iterated projection -/
@[expose] public section
noncomputable section
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
attribute [local instance] firstCoordinateLeftAction

/-- The exact comma-transition square commutes through the homotopy obtained
by realizing its actual natural transformation, in arbitrary universes. -/
def iteratedCommaTranslationHomotopy {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y) :
    ((classifyingSpaceMapUniversal (CostructuredArrow.map
      (S := iteratedSecondProjection (C := C) (D := D))
      (ActionLocalization.mkHom ⟨s, g⟩))).comp
        (classifyingSpaceMapUniversal (iteratedCommaEntry X))).Homotopy
      ((classifyingSpaceMapUniversal (iteratedCommaEntry Y)).comp
        (translationClassifyingHomotopyEquiv s).symm.toFun) := by
  have H := classifyingSpaceUniversalHomotopy (iteratedCommaTranslation s g)
  refine H.cast (classifyingSpaceMapUniversal_comp _ _) ?_
  rw [classifyingSpaceMapUniversal_comp, classifyingSpaceMapUniversal_eq]
  rfl

end Quillen.GroupCompletion.Localization
