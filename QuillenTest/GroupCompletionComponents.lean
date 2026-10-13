/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.GroupCompletion.ConnectedComponents
public import Quillen.KTheory.Plus.ProjectiveGroupCompletion
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers for actual categorical component groups

The generic group requires neither a groupoid nor cancellation. Its pair
formula retains the original denominator arrow. Specializations include finite
projective modules over arbitrary noncommutative rings and the zero ring.
These are categorical components; topological component classification is a
separate bridge.
-/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory Quillen Quillen.FiniteProjectiveModule
open Quillen.GroupCompletion.Localization
universe u v

section Generic
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

example : AddCommGroup (CategoryTheory.ConnectedComponents (GroupCompletion.Localization C C)) :=
  inferInstance

example (A B : C) : componentClass (⟨(A, B)⟩ : GroupCompletion.Localization C C) =
    componentUnitClass B - componentUnitClass A :=
  componentClass_pair_eq_sub A B

example (A B : C) :
    unitEntry.obj B ⟶ (⟨(A, B)⟩ : GroupCompletion.Localization C C) ⊗ unitEntry.obj A :=
  componentDenominatorArrow A B

example (P Q : C) :
    componentUnitClass (P ⊗ Q) = componentUnitClass P + componentUnitClass Q :=
  componentUnitClass_tensor P Q

example (X : GroupCompletion.Localization C C) :
    componentClass (switch.obj X) = -componentClass X := componentClass_switch X

example (a : Components C) : -a + a = 0 := components_neg_add_cancel a
end Generic

section Projective
attribute [local instance] categoryDirectSumMonoidal categoryDirectSumSymmetric
  directSumMonoidal directSumSymmetric
variable (R : Type u) [Ring R]

example : AddCommGroup (CategoryTheory.ConnectedComponents (GroupCompletionCategory R)) :=
  inferInstanceAs (AddCommGroup (Components (IsoCategory R)))

example (A B : IsoCategory Rᵐᵒᵖ) :
    componentClass (completionPair Rᵐᵒᵖ A B) = componentUnitClass B - componentUnitClass A :=
  componentClass_pair_eq_sub A B

example : AddCommGroup (CategoryTheory.ConnectedComponents (GroupCompletionCategory (ZMod 1))) :=
  inferInstanceAs (AddCommGroup (Components (IsoCategory (ZMod 1))))
end Projective
