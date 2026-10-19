/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputTargetFace
import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputConeSource
import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputLaurentFace

/-! Regression checks for complete original target and Laurent faces and strict cone input. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.GlobalBassEvaluationInputTarget
open GlobalBassEvaluation GlobalSectionChangeIndex Quillen.NativePathCells
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The full overlap seam is an equality of original carrier parameters before evaluation. -/
theorem full_pasted_seam (s : unitInterval) :
    InputMixedDesc.postSquareParameter g (1, s) = InputRawPastedParameter.parameter g (0, s) :=
  InputRawPastedSeam.seam g s

/-- Both complete comparison halves keep their original clocks. -/
theorem original_halves (r s : unitInterval) :
    InputTargetFace.parameter g (lower r, s) = InputMixedDesc.postSquareParameter g (r, s) ∧
      InputTargetFace.parameter g (upper r, s) = InputRawPastedParameter.parameter g (r, s) :=
  ⟨InputTargetFace.parameter_lower g r s, InputTargetFace.parameter_upper g r s⟩

/-- Every level recovers the literal original pasted comparison on the strict cylinder. -/
theorem whole_original_target (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (InputTargetFace.parameter g) n =
      ((InputComparisonTracks.target g).level n).comp
        (InputTargetFace.cylinderParameter (Y := Y) n) :=
  InputTargetFace.whole_native g n

/-- The strict input retains the entire original X descent surface. -/
theorem original_source_cylinder (n : ℕ) (r s : unitInterval)
    (x : (GlobalSchemeLaurentTrack.diagram.obj (op Y)).space n) :
    (InputComparisonTracks.source g).level n
      (r, HomotopyPushout.cylinder (sectionMap (projection.app Y))
        (sectionMap (projection.app Y)) n (s, x)) =
      (descPasting X).toSquare.level n (r, (s, (sectionMap g).map n x)) :=
  InputComparisonTracks.source_cylinder g n r s x

/-- The Laurent carrier face is literally constant along the independent cylinder height. -/
theorem laurent_height (q s : unitInterval) :
    InputLaurentFace.parameter g (q, s) = InputLaurentFace.curve g q :=
  InputLaurentFace.parameter_apply g q s

/-- Strict cone precomposition adds no constant half to the original source map. -/
theorem literal_strict_cone :
    InputConeSource.strictConeMap g ≫ coneEvaluation X = InputConeSource.directConeMap g :=
  InputConeSource.strict_comp_evaluation g

/-- The whole literal identification also retains the original parameter-looped maps. -/
theorem literal_strict_loop :
    parameterLoopingMap (InputConeSource.strictConeMap g) ≫ stepEvaluation X =
      parameterLoopingMap (InputConeSource.directConeMap g) :=
  InputConeSource.strict_loop_comp_evaluation g

end QuillenTest.GlobalBassEvaluationInputTarget
