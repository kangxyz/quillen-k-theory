/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.SmallModel.Exact
public import Aglib.CategoryTheory.SmallModel.Localization
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor

/-! # The actual Serre kernel of a small-model localization functor -/
@[expose] public section
open CategoryTheory.ExactCategory
noncomputable section
universe w v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace Quillen.SmallModelGLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure D))
  [PreservesFiniteLimits F.toFunctor] [PreservesFiniteColimits F.toFunctor]
  [F.toFunctor.IsLocalization F.toFunctor.kernel.isoModSerre]

/-- The actual Serre kernel in the chosen source small model. -/
abbrev supported : ObjectProperty (SmallModel.{w} C) :=
  (CategoryTheory.SmallModel.functor F.toFunctor).kernel

end Quillen.SmallModelGLocalization
