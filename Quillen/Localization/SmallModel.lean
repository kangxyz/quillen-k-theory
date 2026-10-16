/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.SmallModel.Exact
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
public import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Exact localizations descend to genuine small models

Conjugating an actual exact localization by the chosen small-model equivalences
preserves its Serre-localization theorem. The kernel is still the actual inverse
image of zero under the conjugated functor. This construction is the underlying
functor used by `CategoryTheory.ExactCategory.ExactFunctor.smallModel`, so its canonical K-map is
  retained.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor


namespace Quillen.SmallModelLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
variable (C : Type u₁) [Category.{v₁} C] [Abelian C] [EssentiallySmall.{w} C]

instance standardExactFunctor_mapQ_isEquivalence :
    (CategoryTheory.SmallModel.abelianExactComparison.{w} C).mapQ.IsEquivalence := by
  apply CategoryTheory.ExactCategory.ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro M N f hf
    rw [abelianExactStructure_smallModel]
    exact hf
  · intro M N f hf
    rw [abelianExactStructure_smallModel]
    exact hf

/-- The canonical identity-induced comparison with standard abelian K-theory
of the chosen small model. -/
def standardKEquiv (n : ℕ) : (abelianExactStructure C).SmallK n ≃*
    (abelianExactStructure (SmallModel.{w} C)).K n :=
  (CategoryTheory.SmallModel.abelianExactComparison C).KEquivOfMapQIsEquivalence n

variable {C} {D : Type u₂} [Category.{v₂} D] [Abelian D] [EssentiallySmall.{w} D]

/-- The standard comparison retains exactly the original canonical
`smallKMap`, rather than an unrelated isomorphism of groups. -/
theorem smallKMap_comparison
    (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure D)) (n : ℕ) :
    (standardKEquiv D n).toMonoidHom.comp (F.smallKMap n) =
      ((CategoryTheory.SmallModel.mapAbelianExactFunctor F).KMap n).comp (standardKEquiv C
        n).toMonoidHom := by
  change ((CategoryTheory.SmallModel.abelianExactComparison D).KMap n).comp (F.smallModel.KMap n) =
    ((CategoryTheory.SmallModel.mapAbelianExactFunctor F).KMap n).comp
      ((CategoryTheory.SmallModel.abelianExactComparison C).KMap n)
  rw [← CategoryTheory.ExactCategory.ExactFunctor.KMap_comp, ←
    CategoryTheory.ExactCategory.ExactFunctor.KMap_comp]
  rfl

end Quillen.SmallModelLocalization
