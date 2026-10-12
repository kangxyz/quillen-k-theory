/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SmallModel.Basic

/-!
# Literal original squares after common-universe lifting

The actual up/down functors cancel, so a strict original functor square stays strict after
lifting its target categories. The original source precomposition is retained without
reassociating a concrete geometric functor during elaboration.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v u₀ v₀ u₁ v₁
namespace Quillen.Waldhausen

/-- A strict original square retains its actual precomposition and target universe lifting. -/
theorem smallModelFunctor_square {C : Type u₀} [Category.{v₀} C]
    {D : Type u₁} [Category.{v₁} D] {E T : Type u} [Category.{v} E] [Category.{v} T]
    (I : C ⥤ D) (F : D ⥤ E) (A : C ⥤ T) (Q : T ⥤ E) (h : I ⋙ F = A ⋙ Q) :
    I ⋙ (F ⋙ AsSmall.up) = (A ⋙ AsSmall.up) ⋙ smallModelFunctor Q :=
  congrArg (fun H => H ⋙ AsSmall.up) h

end Quillen.Waldhausen
