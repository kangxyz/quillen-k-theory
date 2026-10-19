/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSpan

/-! Regression checks for literal input endpoints and unpaused polynomial-span evaluation. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace QuillenTest.GlobalBassEvaluationInputSpan
open GlobalBassEvaluation GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Both ends are the actual composites, evaluated on an arbitrary original quotient point. -/
theorem literal_endpoints (n : ℕ) (x : (StrictSquare.span (sectionSquare Y)).space n) :
    (inputSpanHomotopy g).level n (0, x) =
      (InputSpan.sectionSpanMap g ≫ spanEvaluation X).map n x ∧
    (inputSpanHomotopy g).level n (1, x) =
      (spanEvaluation Y ≫ GlobalRawBass.spanMap g).map n x :=
  ⟨(inputSpanHomotopy g).at_zero n x, (inputSpanHomotopy g).at_one n x⟩

/-- The entire original double cylinder keeps both independent parameters. -/
theorem whole_cylinder (n : ℕ) (r s : unitInterval)
    (x : (GlobalSchemeLaurentTrack.diagram.obj (op Y)).space n) :
    (inputSpanHomotopy g).level n
      (r, HomotopyPushout.cylinder (sectionMap (projection.app Y))
        (sectionMap (projection.app Y)) n (s, x)) =
      (InputSpan.cylinderSquare g).level n (r, (s, x)) :=
  inputSpanHomotopy_cylinder g n r s x

/-- Every left-chart time is the original polynomial evaluation time. -/
theorem unpaused_left_chart (n : ℕ) (r : unitInterval)
    (x : (GlobalSchemeLaurentTrack.diagram.obj (op (polynomial.obj Y))).space n) :
    (inputSpanHomotopy g).level n
      (r, (HomotopyPushout.inl (sectionMap (projection.app Y))
        (sectionMap (projection.app Y))).map n x) =
      (HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (projection.app X))
        (boundedFlatPerfectPrespectrumMap (projection.app X))).map n
          ((evaluationComparison (polynomial.map g)).level n (r, x)) :=
  inputSpanHomotopy_inl g n r x

/-- Every right-chart time is the same original polynomial evaluation time. -/
theorem unpaused_right_chart (n : ℕ) (r : unitInterval)
    (x : (GlobalSchemeLaurentTrack.diagram.obj (op (polynomial.obj Y))).space n) :
    (inputSpanHomotopy g).level n
      (r, (HomotopyPushout.inr (sectionMap (projection.app Y))
        (sectionMap (projection.app Y))).map n x) =
      (HomotopyPushout.inr (boundedFlatPerfectPrespectrumMap (projection.app X))
        (boundedFlatPerfectPrespectrumMap (projection.app X))).map n
          ((evaluationComparison (polynomial.map g)).level n (r, x)) :=
  inputSpanHomotopy_inr g n r x

end QuillenTest.GlobalBassEvaluationInputSpan
