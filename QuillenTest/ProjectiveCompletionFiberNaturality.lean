/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.KTheory.Plus.ProjectiveCompletionFiberNaturality
import Quillen.Topology.HomotopyFiber.BasedSquareMap
import Mathlib.Data.ZMod.Basic

/-! # Clients of the original all-points completion comparison square -/

noncomputable section
open CategoryTheory
open scoped Topology
open Quillen Quillen.FiniteProjectiveModule
universe u
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
  rightBaseChangeCoreMonoidal

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    ((completionNormalizedFiberMap f).comp
      (completionToOriginalQHomotopyFiber Rᵐᵒᵖ)).Homotopy
    ((completionToOriginalQHomotopyFiber Sᵐᵒᵖ).comp (completionBaseChangeMap f)) :=
  completionFiberNaturality f

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (x : ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ)) :
    completionFiberNaturality f (0, x) =
      completionNormalizedFiberMap f (completionToOriginalQHomotopyFiber Rᵐᵒᵖ x) :=
  (completionFiberNaturality f).apply_zero x

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (x : ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ)) :
    completionFiberNaturality f (1, x) =
      completionToOriginalQHomotopyFiber Sᵐᵒᵖ (completionBaseChangeMap f x) :=
  (completionFiberNaturality f).apply_one x

example :
    ((completionNormalizedFiberMap (Int.castRingHom (ZMod 1))).comp
      (completionToOriginalQHomotopyFiber ℤᵐᵒᵖ)).Homotopy
    ((completionToOriginalQHomotopyFiber (ZMod 1)ᵐᵒᵖ).comp
      (completionBaseChangeMap (Int.castRingHom (ZMod 1)))) :=
  completionFiberNaturality (Int.castRingHom (ZMod 1))

-- The original strict-square API remains available beside the homotopy-square API.
example {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] {p : C(X, A)} {q : C(Y, B)}
    (f : C(X, Y)) (g : C(A, B)) (sq : g.comp p = q.comp f)
    (hf : IsWeakHomotopyEquivalence f) (hg : IsWeakHomotopyEquivalence g)
    (a : A) (b : B) (hb : g a = b) :
    IsWeakHomotopyEquivalence (HomotopyFiber.mapAt f g sq a b hb) :=
  HomotopyFiber.mapAt_weak f g sq hf hg a b hb
