/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSpanParameterWhole
import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSpanParameterChart
import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputChartTargetSeams
import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSpanParameterPaths

/-! Regression checks for the original full span family and its proved carrier seams. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.GlobalBassEvaluationInputSpanNative
open GlobalBassEvaluation GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The complete continuous span family is the original cylinder homotopy at every level. -/
theorem whole_original_span (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (InputSpanParameterWord.parameter g) n =
    ((GlobalRawBass.comparison X).map n).comp
      (((inputSpanHomotopy g).level n).comp
        ⟨fun z => (z.1.1, HomotopyPushout.cylinder
          (sectionMap (projection.app Y)) (sectionMap (projection.app Y)) n (z.1.2, z.2)),
          by fun_prop⟩) :=
  InputSpanParameterWhole.native g n

/-- Both scalar times and the genuine level-zero loop input survive original collapse. -/
theorem degree_zero_original_span
    (x : (prespectrum (globalModel.obj (op Y))).space 0) (r s : unitInterval) :
    InputSpanParameterCells.ev g 0 x (InputSpanParameterWord.parameter g (r, s)) =
      (GlobalRawBass.comparison X).map 0
        ((InputSpan.cylinderSquare g).level 0 (r, (s, x))) :=
  InputSpanParameterWhole.parameter_native g 0 x r s

/-- The whole source seam is identified before any native evaluation. -/
theorem full_source_seam (s : unitInterval) :
    InputMixedDesc.preSquareParameter g (1, s) =
      InputSpanParameterWord.parameter g (0, s) :=
  InputSpanParameterSeams.source g s

/-- Both full terminal chart seams retain the independent comparison time. -/
theorem full_span_chart_seams (q : unitInterval) :
    InputSpanParameterWord.parameter g (q, 0) =
        InputChartSquareParameter.plusParameter g (q, 1) ∧
      InputSpanParameterWord.parameter g (q, 1) =
        InputChartSquareParameter.minusParameter g (q, 1) :=
  ⟨InputSpanParameterSeams.plus g q, InputSpanParameterSeams.minus g q⟩

/-- Both original source chart seams retain their complete carrier parameters. -/
theorem full_source_chart_seams (r : unitInterval) :
    InputMixedDesc.preSquareParameter g (r, 0) =
        InputChartSquareParameter.plusParameter g (0, r) ∧
      InputMixedDesc.preSquareParameter g (r, 1) =
        InputChartSquareParameter.minusParameter g (0, r) :=
  ⟨InputChartFaceSeams.pre_plus g r, InputChartFaceSeams.pre_minus g r⟩

/-- Both original target chart seams retain the nested raw-square half clocks. -/
theorem full_target_chart_seams (r : unitInterval) :
    InputTargetFace.parameter g (r, 0) =
        InputChartSquareParameter.plusParameter g (1, r) ∧
      InputTargetFace.parameter g (r, 1) =
        InputChartSquareParameter.minusParameter g (1, r) :=
  ⟨InputChartTargetSeams.plus g r, InputChartTargetSeams.minus g r⟩

/-- All five actual raw nodes agree as full arrows with their selected reference anchors. -/
theorem full_raw_nodes (k : laurent ⟶ polynomial)
    (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)
    (i : Fin 5) :
    InputSpanParameterNodes.nodes g k hk (InputCommutingRawNodes.rawIndex i) =
      InputChartReference.rawNode g k hk (ProjectionRectangleSquareRows.polynomialRow i) :=
  InputSpanTargetNodes.raw_nodes g k hk i

/-- The entire moving-input normalization family is the original split composition path. -/
theorem full_normalization (k : laurent ⟶ polynomial)
    (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z) (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (InputSpanParameterPrism.parameter g k hk) n =
      ((boundedFlatPerfectPrespectrumCompHomotopy (k.app X) (projection.app X)).level n).comp
        (InputSpanParameterPrism.rawInput g n) :=
  InputSpanParameterPrism.whole_native g k hk n

/-- Every stage of the original five-piece reassociation keeps its original two times. -/
theorem original_reassociation (n : ℕ)
    (x : (prespectrum (globalModel.obj (op Y))).space n) (r s : unitInterval) :
    InputSpanParameterCells.ev g n x (InputSpanParameterWord.reassociation g (r, s)) =
      (GlobalRawBass.comparison X).map n
        ((InputSpanParameterAssoc.reassociationNative g).level n (r, (s, x))) :=
  InputSpanParameterAssoc.reassociation_native g n x r s

end QuillenTest.GlobalBassEvaluationInputSpanNative
