/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedTransitionFace
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedEvaluationUnitNerve

/-! Independent clients of the prescribed third word and exact original evaluation-unit surface. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PerfectComplexes
open scoped Topology unitInterval
universe u
namespace Consumer.GlobalBassEvaluationInputSeedCarrier
open GlobalBassEvaluation GlobalSectionChangeIndex CommonReferenceNerve
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The whole original third piece is recovered even at the original degree-zero loop space. -/
theorem degree_zero_third_piece (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space 0) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map 0
      (CutOpenCarrier.nativeEval (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
        (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g)
        0 (InputSeedTransitionFace.parameter g (r, s)) x) =
      Path.toContinuousMap ((InputSeedWords.transitionThird g).level 0 (r, x)) s :=
  InputSeedTransitionFace.native g 0 r s x

/-- All original unit pastings retain their complete four-node family in every degree. -/
theorem whole_unit_family (r : (Γ(X, ⊤))ˣ) (n : ℕ) :
    InputSeedEvaluationUnit.family g r n =
      ((evaluationUnitPasting g r).level n).toContinuousMap :=
  InputSeedEvaluationUnit.family_eq g r n

/-- Arbitrary native inputs see the actual reference-nerve unit surface at independent times. -/
theorem whole_unit_nerve (r : (Γ(X, ⊤))ˣ) (n : ℕ) (s t : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    pointwisePrespectrumFamily (InputSeedEvaluationUnit.sourceMap g) n
      (InputSeedEvaluationUnit.parameter g r (s, t)) x =
      (evaluationUnitPasting g r).level n (s, (t, x)) :=
  InputSeedEvaluationUnit.parameter_native g r n s t x

end Consumer.GlobalBassEvaluationInputSeedCarrier
