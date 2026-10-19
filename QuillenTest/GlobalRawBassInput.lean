/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeed

/-! Regression checks for the original global raw Bass scheme-arrow map and seed. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace QuillenTest.GlobalRawBassInput
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The looped map is the pointwise image under the genuine geometric cone-square map. -/
theorem looped_laurent_inclusion (n : ℕ) (s : unitInterval)
    (x : (parameterLooping
      (originalPrespectrum (boundedFlatPerfectWaldhausen (laurent.obj Y)))).space n) :
    Path.toContinuousMap (((parameterLoopingMap (mappingConeInclusion (comparison Y))) ≫
      GlobalRawBass.map g).map n x) s =
      (mappingConeInclusion (comparison X)).map n
        ((boundedFlatPerfectPrespectrumMap (laurent.map g)).map n
          (Path.toContinuousMap x s)) := rfl

/-- The whole positive source-null comparison keeps its original final moving boundary. -/
theorem null_last_face (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    (InputNull.originalNullComparison g).level n (1, (s, x)) =
      ((InputNull.laurentMovement g).trans (InputNull.originalNewNull g)).level n (s, x) :=
  ((InputNull.originalNullComparison g).level n).apply_one (s, x)

/-- Source-null comparison, output-loop and spectrum structure times remain independent. -/
theorem raw_seed_structure (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    Path.toContinuousMap ((transitionInputHomotopy g).level (n + 1)
      (r, (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).structureMap n x t)) s =
      Path.toContinuousMap ((step X).structureMap n
        ((transitionInputHomotopy g).level n (r, x)) t) s :=
  congrArg (fun p => Path.toContinuousMap p s) ((transitionInputHomotopy g).comm n r x t)

/-- The two original input/evaluation routes compare on the actual initial seed. -/
theorem evaluated_seed_input :
    Nonempty (Homotopy
      ((GlobalBassEvaluation.strictSeed Y ≫ GlobalBassEvaluation.stepEvaluation Y) ≫
        GlobalRawBass.map g)
      (GlobalBassEvaluation.sectionMap g ≫
        (GlobalBassEvaluation.strictSeed X ≫ GlobalBassEvaluation.stepEvaluation X))) :=
  ⟨GlobalBassEvaluation.inputSeedHomotopy g⟩

end QuillenTest.GlobalRawBassInput
