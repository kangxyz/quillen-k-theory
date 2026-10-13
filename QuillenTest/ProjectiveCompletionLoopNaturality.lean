/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.KTheory.Plus.ProjectiveCompletionLoopNaturality
import Quillen.KTheory.Plus.ProjectiveCompletionZeroLoops
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

/-! # Actual standard homotopy endpoints and specified zero tracks -/

noncomputable section

open CategoryTheory Quillen Quillen.FiniteProjectiveModule
open Quillen.FiniteProjectiveModule.StableCompletion
open scoped Topology

universe u

attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
  rightBaseChangeCoreMonoidal

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (x : ClassifyingSpace (Completion R)) :
    completionToOriginalQLoopsBaseChangeHomotopy f (0, x) =
      basedLoopMap (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
        (completionNormalizedQ_basepoint f)
        (completionToOriginalQLoops Rᵐᵒᵖ (stageObject R 0) x) :=
  (completionToOriginalQLoopsBaseChangeHomotopy f).apply_zero x

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (x : ClassifyingSpace (Completion R)) :
    completionToOriginalQLoopsBaseChangeHomotopy f (1, x) =
      completionToOriginalQLoops Sᵐᵒᵖ (stageObject S 0) (completionBaseChangeMap f x) :=
  (completionToOriginalQLoopsBaseChangeHomotopy f).apply_one x

-- The whole homotopy has values in the original based loop space at every point.
example {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (x : ClassifyingSpace (Completion R)) (t : unitInterval) :
    completionToOriginalQLoopsBaseChangeHomotopy f (t, x) 0 =
      classifyingSpacePoint (exactStructure Sᵐᵒᵖ).qZero :=
  (completionToOriginalQLoopsBaseChangeHomotopy f (t, x)).source

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (x : ClassifyingSpace (Completion R)) (t : unitInterval) :
    completionToOriginalQLoopsBaseChangeHomotopy f (t, x) 1 =
      classifyingSpacePoint (exactStructure Sᵐᵒᵖ).qZero :=
  (completionToOriginalQLoopsBaseChangeHomotopy f (t, x)).target

-- Both restricted basepoint tracks retain their specified ambient values.
example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (t : unitInterval) :
    (zeroCompletionBaseChangeBasepointPath f t).val =
      completionBaseChangeBasepointPath f t := rfl

example (R : Type u) [Ring R] (t : unitInterval) :
    (zeroCompletionToOriginalQLoopsBasepointPath R t).val =
      completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ (stageObject R 0) t := rfl

-- No nontrivial-ring hypothesis is introduced by the actual continuous homotopy.
example (x : ClassifyingSpace (Completion ℤ)) :
    Joined
      (basedLoopMap
        (classifyingSpaceMap (rightBaseChangeExact (Int.castRingHom (ZMod 1))).normalizedQ).hom
        (completionNormalizedQ_basepoint (Int.castRingHom (ZMod 1)))
        (completionToOriginalQLoops ℤᵐᵒᵖ (stageObject ℤ 0) x))
      (completionToOriginalQLoops (ZMod 1)ᵐᵒᵖ (stageObject (ZMod 1) 0)
        (completionBaseChangeMap (Int.castRingHom (ZMod 1)) x)) :=
  ⟨(completionToOriginalQLoopsBaseChangeHomotopy (Int.castRingHom (ZMod 1))).evalAt x⟩

-- This same construction applies to genuinely noncommutative coefficient rings.
example :
    ((basedLoopMap
      (classifyingSpaceMap
        (rightBaseChangeExact (RingHom.id (Matrix (Fin 2) (Fin 2) ℤ))).normalizedQ).hom
      (completionNormalizedQ_basepoint (RingHom.id (Matrix (Fin 2) (Fin 2) ℤ)))).comp
        (completionToOriginalQLoops (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ
          (stageObject (Matrix (Fin 2) (Fin 2) ℤ) 0))).Homotopy
    ((completionToOriginalQLoops (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ
      (stageObject (Matrix (Fin 2) (Fin 2) ℤ) 0)).comp
        (completionBaseChangeMap (RingHom.id (Matrix (Fin 2) (Fin 2) ℤ)))) :=
  completionToOriginalQLoopsBaseChangeHomotopy (RingHom.id (Matrix (Fin 2) (Fin 2) ℤ))
