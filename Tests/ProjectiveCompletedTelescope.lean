/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
import Quillen.KTheory.Plus.ProjectiveCompletedTelescope

/-! # Original completed-stage homotopy and local-coefficient comparison -/

open CategoryTheory Quillen Quillen.FiniteProjectiveModule Quillen.LocalCoefficients
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
  projectiveTelescopeAction
universe u
noncomputable section

example (R : Type u) [Ring R] (n : ℕ) :
    (projectiveCompletionStageHomotopyEquiv R n).toFun =
      classifyingSpaceMapUniversal (projectiveCompletionStage R n) :=
  projectiveCompletionStageHomotopyEquiv_toFun R n

example (R : Type u) [Ring R] (n : ℕ)
    (A : System.{u + 1, u + 1} (ClassifyingSpace (ProjectiveTelescopeLocalization R))) (d : ℕ) :
    IsIso (pushforwardHomologyMap (classifyingSpaceMapUniversal (projectiveCompletionStage R n))
      A d) := projectiveCompletionStage_localHomology_isIso R n A d

example (R : Type u) [Ring R] :
    IsWeakHomotopyEquivalence
      (classifyingSpaceMapUniversal (projectiveCompletionStage R 0)) :=
  projectiveCompletionStage_isWeakHomotopyEquivalence R 0
