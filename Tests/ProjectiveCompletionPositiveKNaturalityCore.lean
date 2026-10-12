/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.KTheory.Plus.ProjectiveCompletionPositiveKNaturality

/-! Core consumers of the unchanged positive comparison and the specified ring-map paths. -/
noncomputable section
open Quillen Quillen.FiniteProjectiveModule
universe u
variable {R S : Type u} [Ring R] [Ring S]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
  rightBaseChangeCoreMonoidal

example (f : R →+* S) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (StableCompletion.ZeroComponent R)
      (StableCompletion.zeroBase R)) :
    StableCompletion.zeroCompletionPositiveKEquiv S n
      (pathTransportMulEquiv (zeroCompletionBaseChangeBasepointPath f) n
        (homotopyGroupMapHom (N := Fin (n + 1)) (zeroCompletionBaseChangeMap f) rfl a)) =
    (rightBaseChangeExact f).KMap (n + 1)
      (StableCompletion.zeroCompletionPositiveKEquiv R n a) :=
  StableCompletion.zeroCompletionPositiveKEquiv_baseChange f n a

example (f : R →+* S)
    (a : HomotopyGroup.Pi 1 (ClassifyingSpace (StableCompletion.Completion R))
      (StableCompletion.zeroPoint R)) :
    completionPositiveKEquiv Sᵐᵒᵖ (StableCompletion.stageObject S 0) 0
      (pathTransportMulEquiv (completionBaseChangeBasepointPath f) 0
        (homotopyGroupMapHom (N := Fin 1) (completionBaseChangeMap f) rfl a)) =
    (rightBaseChangeExact f).KMap 1
      (completionPositiveKEquiv Rᵐᵒᵖ (StableCompletion.stageObject R 0) 0 a) :=
  completionPositiveKEquiv_baseChange f 0 a
