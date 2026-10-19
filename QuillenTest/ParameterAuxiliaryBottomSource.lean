/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryBottomSource

/-! # The original bottom-source map is invertible on every finite S-stage diagram -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
universe u
namespace QuillenTest.ParameterAuxiliaryBottomSource

/-- Every original finite S-stage retains invertibility of the actual bottom-source map. -/
theorem toBasic_stage_isIso (Q : Scheme.{u}) (U : Q.Opens) (n : ℕ) :
    IsIso (Functor.whiskerRight (toBasic U.ι ⊥) (stages n)) := by
  infer_instance

end QuillenTest.ParameterAuxiliaryBottomSource
