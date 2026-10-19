/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedInputFace

/-! Independent consumers of the original whole input-first face and its complete edge words. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PerfectComplexes
open scoped Topology unitInterval
universe u
namespace Consumer.GlobalBassEvaluationInputSeedInputFace
open GlobalBassEvaluation GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The entire degree-zero first face keeps both independent scalar times. -/
theorem degree_zero_face (r s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space 0) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map 0
      (InputSeedInputNull.nativeEval g 0 (InputSeedInputFace.parameter g (r, s)) x) =
      Path.toContinuousMap ((InputSeedWords.inputFirst g).level 0 (r, x)) s :=
  InputSeedInputFace.native g 0 r s x

/-- A downstream join can use the full source carrier word before evaluating it. -/
theorem original_source_word (n : ℕ) (s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (InputSeedInputNull.nativeEval g n (InputSeedInputFace.sourceWord g s) x) =
      (InputNaturality.coneHomotopy g).level n
        (0, Path.toContinuousMap ((strictSeed Y).map n x) s) := by
  rw [← InputSeedInputFace.source]
  exact (InputSeedInputFace.native g n 0 s x).trans
    (InputSeedWords.inputFirst_apply g n 0 s x)

/-- The original terminal word has the full target-cone evaluation, not only matching endpoints. -/
theorem original_target_word (n : ℕ) (s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (InputSeedInputNull.nativeEval g n (InputSeedInputFace.targetWord g s) x) =
      (InputNaturality.coneHomotopy g).level n
        (1, Path.toContinuousMap ((strictSeed Y).map n x) s) := by
  rw [← InputSeedInputFace.target]
  exact (InputSeedInputFace.native g n 1 s x).trans
    (InputSeedWords.inputFirst_apply g n 1 s x)

/-- No comparison time identifies the two actual carrier boundary tips. -/
theorem boundary_sheets_distinct (r : I) :
    InputSeedInputFace.parameter g (r, 0) ≠ InputSeedInputFace.parameter g (r, 1) := by
  rw [InputSeedInputFace.zero, InputSeedInputFace.one]
  exact InputSeedCarrier.tips_distinct g

end Consumer.GlobalBassEvaluationInputSeedInputFace
