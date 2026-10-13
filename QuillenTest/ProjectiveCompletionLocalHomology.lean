/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.KTheory.Plus.ProjectiveCompletionLocalHomology
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Matrix.Basic

/-! # Consumers of the original all-target-system completion comparison -/
open CategoryTheory Quillen Quillen.LocalCoefficients
open Quillen.FiniteProjectiveModule Quillen.FiniteProjectiveModule.StableFreeRight
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
universe u

example (R : Type u) [Ring R]
    (A : System.{u + 1, u + 1} (ClassifyingSpace (StableCompletion.Completion R))) :
    QuasiIso (pushforwardChainMap (classifyingSpaceMapUniversal (completionFunctor R)) A) :=
  completionFunctor_localCoefficients_quasiIso R A

example (R : Type u) [Ring R]
    (A : System.{u + 1, u + 1} (ClassifyingSpace (StableCompletion.Completion R))) (n : ℕ) :
    IsIso (pushforwardHomologyMap (classifyingSpaceMapUniversal (completionFunctor R)) A n) :=
  completionFunctor_localHomology_isIso R A n

example (A : System.{1, 1} (ClassifyingSpace (StableCompletion.Completion (ZMod 1)))) :
    QuasiIso (pushforwardChainMap
      (classifyingSpaceMapUniversal (completionFunctor (ZMod 1))) A) :=
  completionFunctor_localCoefficients_quasiIso (ZMod 1) A

example (A : System.{1, 1}
    (ClassifyingSpace (StableCompletion.Completion (Matrix (Fin 2) (Fin 2) ℤ)))) :
    QuasiIso (pushforwardChainMap
      (classifyingSpaceMapUniversal (completionFunctor (Matrix (Fin 2) (Fin 2) ℤ))) A) :=
  completionFunctor_localCoefficients_quasiIso (Matrix (Fin 2) (Fin 2) ℤ) A
