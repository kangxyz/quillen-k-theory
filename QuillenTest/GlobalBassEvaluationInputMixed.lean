/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputRectanglePreNodes
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputMixedDesc

/-! Regression checks for the complete mixed nodes and the unchanged whole native faces. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.GlobalBassEvaluationInputMixed
open GlobalBassEvaluation GlobalSectionChangeIndex
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- Shared full nodes identify every point of the original normalization triangle. -/
theorem normalization_face (z : StdSimplex ℝ (Fin 3)) :
    CommonReferenceNerve.parameter (InputTripleNodes.sourceMap c q p)
      (InputTripleNodes.postNode c q p)
      (StdSimplex.map (InputSimplex.triangleFace 1 2 4 (by decide) (by decide)).toOrderHom z) =
    CommonReferenceNerve.parameter (InputTripleNodes.sourceMap c q p)
      (InputRectangleNodes.rawNode p q p' q' a b c hp hq)
      (StdSimplex.map InputRectangleNodes.normalizationFace.toOrderHom z) :=
  InputRectangleNodes.normalization_parameter p q p' q' a b c hp hq z

/-- The X-side actual evaluation bridge is retained in the complete raw intermediate node. -/
theorem converted_intermediate :
    InputRectangleNodes.preIntermediateNode p q p' q' a b c hp hq =
      InputRectangleNodes.rawNode p q p' q' a b c hp hq 16 :=
  InputRectangleNodes.pre_intermediate_node p q p' q' a b c hp hq

/-- The entire raw rectangle has both old independent clocks at every original level. -/
theorem whole_rectangle (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op A))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputTripleNodes.sourceMap c q p)
      (InputRectangleNodes.rawParameter p q p' q' a b c hp hq) n ((r, s), x) =
    (boundedFlatDoubleSquareTrackComparison p q p' q' a b c hp hq).level n
      (r, (s, (prespectrumMap (evaluationModel (op A))).map n x)) :=
  InputRectangleNodes.raw_parameter_native p q p' q' a b c hp hq n r s x

/-- The whole selected X descent at original level zero is not replaced by an edge filler. -/
theorem whole_pre_desc_square_zero {X Y : Scheme.{u}} (g : X ⟶ Y) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space 0) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (InputMixedDesc.preSquareParameter g) 0 ((r, s), x) =
    (descPasting X).toSquare.level 0 (r, (s, (prespectrumMap (globalModel.map g.op)).map 0 x)) :=
  InputMixedDesc.pre_square_parameter_native g 0 r s x

end QuillenTest.GlobalBassEvaluationInputMixed
