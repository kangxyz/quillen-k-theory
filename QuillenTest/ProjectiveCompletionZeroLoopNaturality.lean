/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.KTheory.Plus.ProjectiveCompletionZeroLoopNaturality
import Mathlib.Data.ZMod.Basic

/-! # The exact zero-component naturality homotopy and its standard ambient values -/

noncomputable section

open CategoryTheory Quillen Quillen.FiniteProjectiveModule
open Quillen.FiniteProjectiveModule.StableCompletion
open scoped Topology

universe u

attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
  rightBaseChangeCoreMonoidal

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (x : ZeroComponent R) :
    zeroCompletionToOriginalQLoopsBaseChangeHomotopy f (0, x) =
      zeroOriginalQLoopsBaseChangeMap f (zeroCompletionToOriginalQLoops R x) :=
  (zeroCompletionToOriginalQLoopsBaseChangeHomotopy f).apply_zero x

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (x : ZeroComponent R) :
    zeroCompletionToOriginalQLoopsBaseChangeHomotopy f (1, x) =
      zeroCompletionToOriginalQLoops S (zeroCompletionBaseChangeMap f x) :=
  (zeroCompletionToOriginalQLoopsBaseChangeHomotopy f).apply_one x

-- The homotopy is literally the standard ambient homotopy restricted at every parameter.
example {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (x : ZeroComponent R) (t : unitInterval) :
    (zeroCompletionToOriginalQLoopsBaseChangeHomotopy f (t, x)).val =
      completionToOriginalQLoopsBaseChangeHomotopy f (t, x.val) := rfl

-- Every intermediate loop belongs to the actual constant-loop component.
example {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (x : ZeroComponent R) (t : unitInterval) :
    completionToOriginalQLoopsBaseChangeHomotopy f (t, x.val) ∈
      pathComponent (Path.refl (classifyingSpacePoint (exactStructure Sᵐᵒᵖ).qZero)) :=
  (zeroCompletionToOriginalQLoopsBaseChangeHomotopy f (t, x)).property

-- The zero ring remains covered by the component-valued continuous homotopy.
example :
    ((zeroOriginalQLoopsBaseChangeMap (Int.castRingHom (ZMod 1))).comp
      (zeroCompletionToOriginalQLoops ℤ)).Homotopy
    ((zeroCompletionToOriginalQLoops (ZMod 1)).comp
      (zeroCompletionBaseChangeMap (Int.castRingHom (ZMod 1)))) :=
  zeroCompletionToOriginalQLoopsBaseChangeHomotopy (Int.castRingHom (ZMod 1))

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (x : ZeroComponent R) (s : unitInterval) :
    (zeroCompletionToOriginalQLoopsBaseChangeHomotopy f (s, x)).val 0 =
      classifyingSpacePoint (exactStructure Sᵐᵒᵖ).qZero :=
  (zeroCompletionToOriginalQLoopsBaseChangeHomotopy f (s, x)).val.source

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (x : ZeroComponent R) (s : unitInterval) :
    (zeroCompletionToOriginalQLoopsBaseChangeHomotopy f (s, x)).val 1 =
      classifyingSpacePoint (exactStructure Sᵐᵒᵖ).qZero :=
  (zeroCompletionToOriginalQLoopsBaseChangeHomotopy f (s, x)).val.target
