/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Plus.StableCompletionBaseChangeNaturality
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers for original telescope change-of-rings naturality

These examples use the actual matrix Grothendieck functor, original projective
completion functor, finite reversal, and stabilization cocone. The zero-rank
comparison is the prescribed inverse-unit isomorphism, including for a ring map
to the zero ring.
-/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory Quillen Quillen.FiniteProjectiveModule
universe u
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal rightBaseChangeMonoidal
variable {R S : Type u} [Ring R] [Ring S]

example (f : R →+* S) :
    StableCompletion.telescopeFunctor R ⋙ completionBaseChange f ≅
      StableGeneralLinear.GrothendieckModel.ringFunctor f ⋙
        StableCompletion.telescopeFunctor S :=
  StableCompletion.telescopeBaseChangeIso f

example (f : R →+* S) (n : ℕ) :
    (completionBaseChange f).map (StableCompletion.stageArrow R n) ≫
        (StableCompletion.stageBaseChangeIso f (n + 1)).hom =
      (StableCompletion.stageBaseChangeIso f n).hom ≫ StableCompletion.stageArrow S n :=
  StableCompletion.stageBaseChangeIso_successor f n

example (f : R →+* S) (n : ℕ) (g : StableGeneralLinear.GL R n) :
    (rightBaseChange f).map (RightMatrix.leftFreeAutEquiv R n g).hom ≫
        (RightMatrix.freeBaseChangeIso f n).hom =
      (RightMatrix.freeBaseChangeIso f n).hom ≫
        (RightMatrix.leftFreeAutEquiv S n (StableGeneralLinear.finiteMap f n g)).hom :=
  RightMatrix.freeBaseChangeIso_left_action f n g

example (f : R →+* S) :
    StableCompletion.stageBaseChangeIso f 0 = completionBaseChangeZeroIso f :=
  StableCompletion.stageBaseChangeIso_zero f

example :
    StableCompletion.telescopeFunctor ℤ ⋙ completionBaseChange (Int.castRingHom (ZMod 1)) ≅
      StableGeneralLinear.GrothendieckModel.ringFunctor (Int.castRingHom (ZMod 1)) ⋙
        StableCompletion.telescopeFunctor (ZMod 1) :=
  StableCompletion.telescopeBaseChangeIso _

example : StableCompletion.stageBaseChangeIso (Int.castRingHom (ZMod 1)) 0 =
    completionBaseChangeZeroIso (Int.castRingHom (ZMod 1)) :=
  StableCompletion.stageBaseChangeIso_zero _
