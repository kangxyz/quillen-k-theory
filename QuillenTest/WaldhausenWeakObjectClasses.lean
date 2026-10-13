/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.WeakRelations

/-! Original weak zigzags and original zero objects determine equalities in the
actual homotopical Waldhausen K₀, before any classical presentation theorem. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen.Waldhausen
universe u v
namespace QuillenTest.WaldhausenWeakObjectClasses

open Quillen
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- A common target under original weak arrows identifies actual canonical K₀ classes. -/
theorem original_weak_zigzag {A B Q : C} (f : A ⟶ Q) (g : B ⟶ Q)
    (hf : W.weq f) (hg : W.weq g) : W.kZeroObjectClass A = W.kZeroObjectClass B :=
  (W.kZeroObjectClass_weak f hf).trans (W.kZeroObjectClass_weak g hg).symm

/-- Changing two objects by original weak arrows preserves their signed difference
in the actual original K₀ group law. -/
theorem original_weak_difference {A B A' B' : C} (f : A ⟶ A') (g : B ⟶ B')
    (hf : W.weq f) (hg : W.weq g) :
    W.kZeroObjectClass A * (W.kZeroObjectClass B)⁻¹ =
      W.kZeroObjectClass A' * (W.kZeroObjectClass B')⁻¹ := by
  rw [W.kZeroObjectClass_weak f hf, W.kZeroObjectClass_weak g hg]

/-- An original acyclic object has trivial actual object-loop class. -/
theorem original_acyclic_object (A : C) (h : W.weq (W.isZero.to_ A)) :
    W.kZeroObjectClass A = 1 :=
  (W.kZeroObjectClass_weak (W.isZero.to_ A) h).symm.trans W.kZeroObjectClass_zero

end QuillenTest.WaldhausenWeakObjectClasses
