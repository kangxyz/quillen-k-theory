/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveExtensionAction

/-! # Fixed-quotient direct-sum action regression tests -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
open Quillen.FiniteProjectiveModule
attribute [local instance] categoryDirectSumMonoidal categoryDirectSumSymmetric
attribute [local instance] directSumMonoidal directSumSymmetric extensionFiberDirectSumAction

variable (R : Type u) [Ring R] (C : Quillen.FiniteProjectiveModule.Category.{u, u} R)

example (S : IsoCategory R) (p : (exactStructure R).ExtensionFiber C) :
    (S ⊙ₗ p).of.obj.hom = coprod.desc (0 : S.of ⟶ C) p.of.obj.hom := rfl

example (S : IsoCategory R) (p : (exactStructure R).ExtensionFiber C) :
    (exactStructure R).deflation (S ⊙ₗ p).of.obj.hom := (S ⊙ₗ p).of.property

example (S T : IsoCategory R) (p : (exactStructure R).ExtensionFiber C) :
    (S ⊗ T) ⊙ₗ p ≅ S ⊙ₗ T ⊙ₗ p := αₗ S T p

example (p : (exactStructure R).ExtensionFiber C) :
    (𝟙_ (IsoCategory R)) ⊙ₗ p ≅ p := λₗ p

example (p : (exactStructure R).ExtensionFiber C) :
    (MonoidalLeftAction.actionRight (IsoCategory R) p).Faithful :=
  extensionActionRight_faithful R C p

example (S : IsoCategory R) (p : (exactStructure R).ExtensionFiber C) :
    (⟨p⟩ : ExtensionActionCategory R C) ⟶ ⟨S ⊙ₗ p⟩ :=
  Quillen.GroupCompletion.ActionLocalization.translation S p

example (p : (exactStructure R).ExtensionFiber C) :
    (⟨p⟩ : ExtensionActionCategory R C) ⟶ ⟨p⟩ := 𝟙 _
