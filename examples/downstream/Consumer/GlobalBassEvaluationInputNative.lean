/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputDescNative

/-! Downstream use of the unchanged whole global evaluation descent face. -/
@[expose] public section
noncomputable section
open AlgebraicGeometry Opposite Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes
open scoped Topology unitInterval
universe u
namespace Consumer.GlobalBassEvaluationInputNative

/-- The actual native relative homotopy has one complete finite categorical parameter. -/
theorem original_desc_face (X : Scheme.{u}) (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (GlobalSectionChangeIndex.globalModel.obj (op X))).space n) :
    prespectrumSimplexFamily (GlobalBassEvaluation.InputChartSimplex.simplex X) n
      (GlobalBassEvaluation.InputChartSimplex.descParameter (r, s), x) =
      (GlobalBassEvaluation.descPasting X).level n (r, (s, x)) :=
  GlobalBassEvaluation.InputChartSimplex.desc_native X n r s x

end Consumer.GlobalBassEvaluationInputNative
