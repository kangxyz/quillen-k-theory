/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.CategoryTheory.GroupCompletion.IsoFiber

/-! # Original isomorphism fibers commute with the actual localization -/
noncomputable section
universe u v u₁ v₁ u₂ v₂
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Quillen Quillen.GroupCompletion Quillen.GroupCompletion.Localization
variable {S : Type u} [Category.{v} S] [MonoidalCategory S]
  {C : Type u₁} [Category.{v₁} C] [MonoidalLeftAction S C]
  {B : Type u₂} [Category.{v₂} B]
local instance : MonoidalLeftAction S B := MonoidalLeftAction.trivial S B
variable (F : C ⥤ B) [F.LaxLeftLinear S]
  [∀ (s : S) (X : C), IsIso (Functor.LaxLeftLinear.μₗ F s X)] (b : B)
attribute [local instance] IsoFiber.monoidalLeftAction
example : Localization S (IsoFiber F b) ≌ IsoFiber (fiberProjection (S := S) F) b :=
  isoFiberEquivalence F b
example : (isoFiberEquivalence (S := S) F b).functor = isoFiberEntry F b := rfl
