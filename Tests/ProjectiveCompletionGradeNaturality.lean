/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Plus.ProjectiveCompletionGradeNaturality

/-! # Consumers of original completion virtual-class naturality -/

@[expose] public section

noncomputable section

universe u

open Quillen.FiniteProjectiveModule
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
  rightBaseChangeCoreMonoidal

variable {R S : Type u} [Ring R] [Ring S]

example (f : R →+* S) (X : StableCompletion.Completion R) :
    completionGrade Sᵐᵒᵖ ((completionBaseChange f).obj X) =
      (rightBaseChangeExact f).grothendieckMap (completionGrade Rᵐᵒᵖ X) :=
  completionGrade_baseChange f X

example (f : R →+* S) (X : StableCompletion.Completion R) :
    (rightBaseChangeExact f).KMap 0 (completionKZeroClass Rᵐᵒᵖ X) =
      completionKZeroClass Sᵐᵒᵖ ((completionBaseChange f).obj X) :=
  completionKZeroClass_baseChange f X

example (X : StableCompletion.Completion R) :
    completionKZeroClass Rᵐᵒᵖ X =
      (exactStructure Rᵐᵒᵖ).kZeroObjectClass X.obj.2.of /
        (exactStructure Rᵐᵒᵖ).kZeroObjectClass X.obj.1.of :=
  completionKZeroClass_eq_objectClasses Rᵐᵒᵖ X
