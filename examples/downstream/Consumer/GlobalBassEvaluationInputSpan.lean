/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSpan

/-! An independent level-zero client of the complete original polynomial-span comparison. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Consumer.GlobalBassEvaluationInputSpan
open GlobalBassEvaluation GlobalSectionChangeIndex

/-- At genuine level zero the whole cylinder and both whole charts retain their original times. -/
theorem original_input_span_zero {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (∀ (r s : unitInterval)
      (x : (GlobalSchemeLaurentTrack.diagram.obj (op Y)).space 0),
      (inputSpanHomotopy g).level 0
        (r, HomotopyPushout.cylinder (sectionMap (projection.app Y))
          (sectionMap (projection.app Y)) 0 (s, x)) =
        (InputSpan.cylinderSquare g).level 0 (r, (s, x))) ∧
    (∀ (r : unitInterval)
      (x : (GlobalSchemeLaurentTrack.diagram.obj (op (polynomial.obj Y))).space 0),
      (inputSpanHomotopy g).level 0
        (r, (HomotopyPushout.inl (sectionMap (projection.app Y))
          (sectionMap (projection.app Y))).map 0 x) =
        (HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (projection.app X))
          (boundedFlatPerfectPrespectrumMap (projection.app X))).map 0
            ((evaluationComparison (polynomial.map g)).level 0 (r, x))) ∧
    (∀ (r : unitInterval)
      (x : (GlobalSchemeLaurentTrack.diagram.obj (op (polynomial.obj Y))).space 0),
      (inputSpanHomotopy g).level 0
        (r, (HomotopyPushout.inr (sectionMap (projection.app Y))
          (sectionMap (projection.app Y))).map 0 x) =
        (HomotopyPushout.inr (boundedFlatPerfectPrespectrumMap (projection.app X))
          (boundedFlatPerfectPrespectrumMap (projection.app X))).map 0
            ((evaluationComparison (polynomial.map g)).level 0 (r, x))) :=
  ⟨inputSpanHomotopy_cylinder g 0, inputSpanHomotopy_inl g 0, inputSpanHomotopy_inr g 0⟩

end Consumer.GlobalBassEvaluationInputSpan
