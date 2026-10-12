/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.KTheory.Plus.ProjectiveCompletionBaseChange
public import Mathlib.Data.ZMod.Basic

/-! # Actual arbitrary-ring completion maps and their original basepoint tracks -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
universe u

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    StableCompletion.Completion R ⥤ StableCompletion.Completion S := completionBaseChange f

example : C(StableCompletion.ZeroComponent (ZMod 1),
    StableCompletion.ZeroComponent (ZMod 1)) :=
  zeroCompletionBaseChangeMap (RingHom.id (ZMod 1))

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    Path (zeroCompletionBaseChangeMap f (StableCompletion.zeroBase R))
      (StableCompletion.zeroBase S) := zeroCompletionBaseChangeBasepointPath f

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (t : unitInterval) :
    (zeroCompletionBaseChangeBasepointPath f t).val =
      completionBaseChangeBasepointPath f t := zeroCompletionBaseChangeBasepointPath_val f t
