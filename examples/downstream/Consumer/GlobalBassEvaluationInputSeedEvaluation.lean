/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedEvaluationConjugation

/-! Independent clients of the original two-tip objectwise evaluation seed. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PerfectComplexes
open scoped Topology unitInterval
universe u
namespace Consumer.GlobalBassEvaluationInputSeedEvaluation
open GlobalBassEvaluation GlobalSectionChangeIndex CommonReferenceNerve
open InputSeedEvaluationCarrier InputSeedEvaluationNull InputSeedEvaluationConjugation
variable (X : Scheme.{u})

/-- Degree zero retains the entire original seed face and its independent output-loop time. -/
theorem degree_zero_seed (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op X))).space 0) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map 0
      (CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
        (ordinary X) (shifted X) 0 (comparison X (r, s)) x) =
      Path.toContinuousMap ((GlobalBassEvaluation.seedHomotopy X).level 0 (r, x)) s :=
  comparison_seed X 0 r s x

/-- The shifted null surface is the original complete surface in every native degree. -/
theorem shifted_original_null (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op X))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
        (ordinary X) (shifted X) n (pastedNull X true (r, s)) x) =
      (GlobalBassEvaluationNull.originalNullComparison X).level n (r, (s, x)) :=
  originalNull_whole X true n r s x

/-- The independent client cannot collapse the two tip edges at any comparison times. -/
theorem distinct_boundary_edges (r t : unitInterval) :
    comparison X (r, 0) ≠ comparison X (t, 1) := by
  rw [comparison_zero, comparison_one]
  exact tips_distinct X

end Consumer.GlobalBassEvaluationInputSeedEvaluation
