/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedNaturality

/-! Independent clients of the actual original mixed seed relative comparison. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Consumer.GlobalBassEvaluationInputSeedNaturality
open GlobalBassEvaluation GlobalSectionChangeIndex CommonReferenceNerve
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original literal routes can be compared without supplying any extra face or filler. -/
def prescribedComparison :
    (InputSeedWords.longRoute g).RelHomotopy (InputSeedWords.shortRoute g) :=
  InputSeedNaturality.comparison g

/-- Prespectrum level zero retains all three independent times and the original two-tip extension. -/
theorem level_zero (r s t : I)
    (x : (prespectrum (globalModel.obj (op Y))).space 0) :
    Path.toContinuousMap ((prescribedComparison g).level 0 (r, (s, x))) t =
      (GlobalRawBass.InputIdentityPositive.inclusion X).map 0
        (CutOpenCarrier.nativeEval (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
          (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g)
          0 ((InputSeedRoutes.surfaces g).boundary.carrier ((r, s), t)) x) :=
  InputSeedNaturality.comparison_apply g 0 r s t x

/-- The whole comparison is compatible with the independent original structure coordinate. -/
theorem structure_time (n : ℕ) (r s t v : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((prescribedComparison g).level (n + 1)
      (r, (s, (prespectrum (globalModel.obj (op Y))).structureMap n x t))) v =
    Path.toContinuousMap ((GlobalRawBass.step X).structureMap n
      ((prescribedComparison g).level n (r, (s, x))) t) v :=
  congrArg (fun p ↦ Path.toContinuousMap p v) ((prescribedComparison g).comm n r s x t)

end Consumer.GlobalBassEvaluationInputSeedNaturality
