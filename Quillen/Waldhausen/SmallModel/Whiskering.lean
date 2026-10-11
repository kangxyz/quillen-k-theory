/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SmallModel.Basic

/-!
# Original universe lifting of whiskered comparisons

The actual `AsSmall` up/down functors cancel in the lifted target. This retains the supplied
functor comparison and its subsequent original normalization comparison.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor
universe u v u₀ v₀
namespace Quillen.Waldhausen

/-- Lift a genuine whiskered comparison through the original small-model functors. -/
def smallModelWhiskerIso {C : Type u₀} [Category.{v₀} C]
    {D E : Type u} [Category.{v} D] [Category.{v} E]
    (A : C ⥤ D) (B : C ⥤ E) (P Q : D ⥤ E) (i : B ≅ A ⋙ P) (j : P ≅ Q) :
    B ⋙ AsSmall.up ≅ (A ⋙ AsSmall.up) ⋙ smallModelFunctor Q :=
  isoWhiskerRight (i ≪≫ isoWhiskerLeft A j) AsSmall.up

end Quillen.Waldhausen
