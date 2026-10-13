/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.GroupCompletionAbelian
public import Quillen.Topology.ClassifyingSpace.StableGeneralLinearCompletionQuotient
public import Mathlib.Data.ZMod.Basic

/-! # All-component monodromy consumers for the actual completion -/

@[expose] public section

open CategoryTheory

universe u v w

example {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (A : Quillen.LocalCoefficients.System.{max u v, w}
      (Quillen.ClassifyingSpace (Quillen.GroupCompletion.Localization C C))) :
    Quillen.LocalCoefficients.AbelianMonodromy A :=
  Quillen.GroupCompletion.Localization.classifyingSpace_abelianMonodromy A

example {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (x : FundamentalGroupoid
      (Quillen.ClassifyingSpace (Quillen.GroupCompletion.Localization C C)))
    (g h : x ⟶ x) : g ≫ h = h ≫ g :=
  Quillen.GroupCompletion.Localization.classifyingSpace_loops_commute x g h

section Ring

attribute [local instance] Quillen.FiniteProjectiveModule.categoryDirectSumMonoidal
  Quillen.FiniteProjectiveModule.directSumMonoidal
  Quillen.FiniteProjectiveModule.directSumSymmetric

example (R : Type u) [Ring R]
    (A : Quillen.LocalCoefficients.System
      (Quillen.ClassifyingSpace (Quillen.FiniteProjectiveModule.StableCompletion.Completion R))) :
    Quillen.LocalCoefficients.AbelianMonodromy A :=
  Quillen.GroupCompletion.Localization.classifyingSpace_abelianMonodromy A

example (A : Quillen.LocalCoefficients.System
    (Quillen.ClassifyingSpace
      (Quillen.FiniteProjectiveModule.StableCompletion.Completion (ZMod 1)))) :
    Quillen.LocalCoefficients.AbelianMonodromy A :=
  Quillen.GroupCompletion.Localization.classifyingSpace_abelianMonodromy A

end Ring
