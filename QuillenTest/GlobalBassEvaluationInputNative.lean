/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputDescNative

/-! Regression tests for the complete original global evaluation descent face. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace QuillenTest.GlobalBassEvaluationInputNative

/-- The complete selected descPasting is evaluated at both original coordinates. -/
theorem whole_desc (X : Scheme.{u}) (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (GlobalSectionChangeIndex.globalModel.obj (op X))).space n) :
    prespectrumSimplexFamily (GlobalBassEvaluation.InputChartSimplex.simplex X) n
      (GlobalBassEvaluation.InputChartSimplex.descParameter (r, s), x) =
      (GlobalBassEvaluation.descPasting X).level n (r, (s, x)) :=
  GlobalBassEvaluation.InputChartSimplex.desc_native X n r s x

/-- The original degree-zero input loop keeps its own independent coordinate. -/
theorem whole_desc_loop (X : Scheme.{u}) (r s q : unitInterval)
    (x : (prespectrum (GlobalSectionChangeIndex.globalModel.obj (op X))).space 0) :
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (laurent.obj X))))
        (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (laurent.obj X)))) from
      prespectrumSimplexFamily (GlobalBassEvaluation.InputChartSimplex.simplex X) 0
        (GlobalBassEvaluation.InputChartSimplex.descParameter (r, s), x)) q =
      (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (laurent.obj X))))
          (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (laurent.obj X)))) from
        (GlobalBassEvaluation.descPasting X).level 0 (r, (s, x))) q :=
  congrArg (fun p : Path
    (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (laurent.obj X))))
    (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (laurent.obj X)))) => p q)
    (whole_desc X 0 r s x)

/-- The complete common carrier retains both actual chart diagrams. -/
theorem both_chart_faces (X : Scheme.{u}) :
    (GlobalBassEvaluation.InputChartSimplex.simplex X).face
      GlobalBassEvaluation.InputChartSimplex.plusFace =
      GlobalBassEvaluation.InputSimplex.simplex (plus.app X) (projection.app X) ∧
    (GlobalBassEvaluation.InputChartSimplex.simplex X).face
      GlobalBassEvaluation.InputChartSimplex.minusFace =
      GlobalBassEvaluation.InputSimplex.simplex (minus.app X) (projection.app X) :=
  ⟨GlobalBassEvaluation.InputChartSimplex.plus_face X,
    GlobalBassEvaluation.InputChartSimplex.minus_face X⟩

end QuillenTest.GlobalBassEvaluationInputNative
