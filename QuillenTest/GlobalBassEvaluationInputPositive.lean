/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputPositiveFactor
import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputPositiveSeed

/-! Regression checks for exact positive support of the fixed input and objectwise seed laws. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace QuillenTest.GlobalBassEvaluationInputPositive
open GlobalBassEvaluation GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Evaluation agrees on every positive cone point, including the original cylinder height. -/
theorem evaluated_positive_point (n : ℕ)
    (x : (mappingCone (InputPositive.strictChart X)).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      ((InputPositive.evaluation X).map n x) =
      (coneEvaluation X).map n ((InputPositive.strictInclusion X).map n x) :=
  congrArg (fun f ↦ f.map n x) (InputPositive.evaluation_factor X)

/-- Actual strict input and whole strict input agree on every supported cone point. -/
theorem strict_positive_input (n : ℕ)
    (x : (mappingCone (InputPositive.strictChart Y)).space n) :
    (InputPositive.strictInclusion X).map n ((InputPositive.strictInput g).map n x) =
      (InputConeSource.strictConeMap g).map n ((InputPositive.strictInclusion Y).map n x) :=
  congrArg (fun f ↦ f.map n x) (InputPositive.strictInput_factor g)

/-- The fixed whole square keeps its actual positive face with both independent times. -/
theorem fixed_whole_positive_face (n : ℕ) (r s : unitInterval)
    (x : (GlobalSchemeLaurentTrack.diagram.obj (op (polynomial.obj Y))).space n) :
    (InputPositive.square g).level n (r, (s, x)) =
      (InputCube.square g).level n
        (r, (s, (HomotopyPushout.inl (sectionMap (projection.app Y))
          (sectionMap (projection.app Y))).map n x)) :=
  InputPositive.square_factor g n r s x

/-- The chosen whole cone homotopy agrees on all supported points at every degree and time. -/
theorem fixed_whole_cone (n : ℕ) (r : unitInterval)
    (x : (mappingCone (InputPositive.strictChart Y)).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      ((InputPositive.coneHomotopy g).level n (r, x)) =
      (InputNaturality.coneHomotopy g).level n
        (r, (InputPositive.strictInclusion Y).map n x) :=
  InputPositive.coneHomotopy_factor g n r x

/-- Input comparison time is independent of the original output-loop evaluation time. -/
theorem independent_input_loop (n : ℕ) (r s : unitInterval)
    (γ : (parameterLooping (mappingCone (InputPositive.strictChart Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (Path.toContinuousMap ((InputPositive.stepHomotopy g).level n (r, γ)) s) =
      Path.toContinuousMap ((InputNaturality.stepHomotopy g).level n
        (r, (parameterLoopingMap (InputPositive.strictInclusion Y)).map n γ)) s :=
  InputPositive.stepHomotopy_factor g n r s γ

/-- The supported strict seed recovers the unchanged whole forward Laurent seed. -/
theorem original_strict_seed :
    InputPositive.strictSeed X ≫ parameterLoopingMap (InputPositive.strictInclusion X) =
      GlobalBassEvaluation.strictSeed X :=
  InputPositive.strictSeed_factor X

/-- The chosen objectwise seed homotopy retains its whole image at both original times. -/
theorem original_objectwise_seed (n : ℕ) (r s : unitInterval)
    (x : (GlobalSchemeLaurentTrack.diagram.obj (op X)).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (Path.toContinuousMap ((InputPositive.seedHomotopy X).level n (r, x)) s) =
      Path.toContinuousMap ((GlobalBassEvaluation.seedHomotopy X).level n (r, x)) s :=
  InputPositive.seedHomotopy_factor X n r s x

/-- The original null-comparison word retains every chosen subdivision and both times. -/
theorem original_null_comparison (n : ℕ) (r s : unitInterval)
    (x : (GlobalSchemeLaurentTrack.diagram.obj (op X)).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      ((InputPositiveNull.originalNullComparison X).level n (r, (s, x))) =
      (GlobalBassEvaluationNull.originalNullComparison X).level n (r, (s, x)) :=
  InputPositiveNull.originalNullComparison_mapped X n x r s

/-- Seed comparison and output-loop time remain separate in the actual conjugation recipe. -/
theorem independent_seed_loop (n : ℕ) (r s : unitInterval)
    (x : (GlobalSchemeLaurentTrack.diagram.obj (op X)).space n) :
    Path.toContinuousMap ((InputPositive.seedHomotopy X).level n (r, x)) s =
      (InputPositive.conjugation X).level n (r, (s, x)) :=
  InputPositive.seedHomotopy_apply X n r s x

end QuillenTest.GlobalBassEvaluationInputPositive
