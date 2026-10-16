/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.SmallModelHomExt

/-! # Original K-zero extensionality retains independent category and target universes -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen.Waldhausen
universe u v w
namespace QuillenTest.SmallModelHomExt

/-- The source object and morphism universes remain independent in the original K-zero group. -/
theorem original_universe_hom_ext {C : Type u} [Category.{v} C] (W : Structure C)
    {H : Type w} [_root_.Group H] (f g : W.K 0 →* H)
    (h : ∀ A, f (W.kZeroObjectClass A) = g (W.kZeroObjectClass A)) : f = g :=
  AlgebraicGrothendieck.kZero_hom_ext_ofSmallModel W f g h

end QuillenTest.SmallModelHomExt
