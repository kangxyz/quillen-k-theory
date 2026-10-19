/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedEvaluationConjugation

/-! Regression checks for both complete original null sheets and the exact evaluation seed. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PerfectComplexes
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.GlobalBassEvaluationInputSeedEvaluation
open GlobalBassEvaluation GlobalSectionChangeIndex CommonReferenceNerve
open InputSeedEvaluationCarrier InputSeedEvaluationNull InputSeedEvaluationConjugation

private theorem loop_start {E F : Quillen.LoopPrespectrum.{u}}
    {f g : E ⟶ parameterLooping F} (H : Quillen.LoopPrespectrum.Homotopy f g) (n : ℕ)
    (x : E.space n) (s : unitInterval) :
    Path.toContinuousMap (H.level n (0, x)) s = Path.toContinuousMap (f.map n x) s :=
  congrArg (fun p ↦ Path.toContinuousMap p s) (H.at_zero n x)

private theorem loop_end {E F : Quillen.LoopPrespectrum.{u}}
    {f g : E ⟶ parameterLooping F} (H : Quillen.LoopPrespectrum.Homotopy f g) (n : ℕ)
    (x : E.space n) (s : unitInterval) :
    Path.toContinuousMap (H.level n (1, x)) s = Path.toContinuousMap (g.map n x) s :=
  congrArg (fun p ↦ Path.toContinuousMap p s) (H.at_one n x)

variable (X : Scheme.{u})

/-- Even independently selected comparison times cannot identify the two actual tip edges. -/
theorem separate_edges (r t : unitInterval) :
    comparison X (r, 0) ≠ comparison X (t, 1) := by
  rw [comparison_zero, comparison_one]
  exact tips_distinct X

/-- The polynomial edge attaches with its whole original reference isomorphism. -/
theorem polynomial_attachment (i : Fin 2) :
    InputChartSimplex.nodes X (polynomialFace.toOrderHom i) =
      attachPostcompNode (polyRef X) (chart X) (laurentRef X) (ordinary X)
        (polynomialNodes X i) := polynomial_nodes X i

/-- Both complete null surfaces recover the same original native comparison independently. -/
theorem two_null_sheets (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
        (ordinary X) (shifted X) n (pastedNull X false (r, s)) x =
      CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
        (ordinary X) (shifted X) n (pastedNull X true (r, s)) x :=
  (originalNull_native X false n r s x).trans (originalNull_native X true n r s x).symm

/-- Each entire null surface also retains the unchanged whole-cone comparison. -/
theorem original_null (e : Bool) (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op X))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
        (ordinary X) (shifted X) n (pastedNull X e (r, s)) x) =
      (GlobalBassEvaluationNull.originalNullComparison X).level n (r, (s, x)) :=
  originalNull_whole X e n r s x

/-- The actual four-node unit surface retains its original two independent clocks. -/
theorem original_unit (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n
      (InputSeedEvaluationNullUnit.unitComparison X (r, s)) x =
      (InputPositive.unitPasting X).level n (r, (s, x)) :=
  InputSeedEvaluationNullUnit.unitComparison_native X n r s x

/-- Both nonconstant boundaries retain the full old and new conjugate words. -/
theorem whole_word_edges (s t : unitInterval) :
    comparison X (0, s) = sourceWord X s ∧ comparison X (1, t) = targetWord X t :=
  ⟨comparison_source X s, comparison_target X t⟩

/-- Every coordinate of the carrier face is the original frozen evaluation seed. -/
theorem original_seed (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op X))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
        (ordinary X) (shifted X) n (comparison X (r, s)) x) =
      Path.toContinuousMap ((GlobalBassEvaluation.seedHomotopy X).level n (r, x)) s :=
  comparison_seed X n r s x

/-- The whole initial word evaluates to the literal original strict seed and step map. -/
theorem strict_seed_boundary (n : ℕ) (s : unitInterval)
    (x : (prespectrum (globalModel.obj (op X))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
        (ordinary X) (shifted X) n (sourceWord X s) x) =
      Path.toContinuousMap ((strictSeed X ≫ stepEvaluation X).map n x) s := by
  have h := comparison_seed X n 0 s x
  rw [comparison_source] at h
  exact h.trans (loop_start (GlobalBassEvaluation.seedHomotopy X) n x s)

/-- The whole final word evaluates to actual base evaluation followed by raw transition. -/
theorem raw_seed_boundary (n : ℕ) (s : unitInterval)
    (x : (prespectrum (globalModel.obj (op X))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
        (ordinary X) (shifted X) n (targetWord X s) x) =
      Path.toContinuousMap ((GlobalBassEvaluation.evaluation X ≫ GlobalRawBass.transition X).map n x) s := by
  have h := comparison_seed X n 1 s x
  rw [comparison_target] at h
  exact h.trans (loop_end (GlobalBassEvaluation.seedHomotopy X) n x s)

end QuillenTest.GlobalBassEvaluationInputSeedEvaluation
