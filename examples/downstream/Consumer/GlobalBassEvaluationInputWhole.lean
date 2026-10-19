/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputNaturality

/-! Independent clients of the actual one-step global input law and its genuine zero level. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Consumer.GlobalBassEvaluationInputWhole
open GlobalBassEvaluation GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Arbitrary scheme input is compared through the actual strict and independent raw maps. -/
theorem whole_input : Nonempty (Homotopy
    ((((Quillen.KTheory.Bass.strictDiagramFunctor squareFunctor).obj
      GlobalSchemeLaurentTrack.diagram).map g.op) ≫ stepEvaluation X)
    (stepEvaluation Y ≫ GlobalRawBass.map g)) :=
  ⟨InputNaturality.stepHomotopy g⟩

/-- The compact target face retains the original loop input at its literal zero level. -/
theorem target_degree_zero :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (InputTargetFace.parameter g) 0 =
      ((InputComparisonTracks.target g).level 0).comp
        (InputTargetFace.cylinderParameter (Y := Y) 0) :=
  InputTargetFace.whole_native g 0

end Consumer.GlobalBassEvaluationInputWhole
