/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationSeed

/-!
# Original global Bass input evaluation on the forward seed

The independently constructed raw scheme-arrow map, its complete raw source-null and unit
comparison, and original evaluation seed comparison give a homotopy on the original initial
seed. This is restricted to that seed. It does not construct naturality of the whole one-step
evaluation, or identify the higher mixed evaluation/input/overlap pasting that would be required
for such a result.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation
open GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The first route retains original evaluation of the seed before actual raw scheme change. -/
def inputSeedEvaluationTrack :
    Homotopy ((strictSeed Y ≫ stepEvaluation Y) ≫ GlobalRawBass.map g)
      (evaluation Y ≫ (GlobalRawBass.transition Y ≫ GlobalRawBass.map g)) :=
  ((seedHomotopy Y).postcomp (GlobalRawBass.map g)).cast rfl (Category.assoc _ _ _)

/-- Raw input naturality and original degree-zero evaluation move the actual forward seed. -/
def inputSeedRawTrack :
    Homotopy (evaluation Y ≫ (GlobalRawBass.transition Y ≫ GlobalRawBass.map g))
      (sectionMap g ≫ (evaluation X ≫ GlobalRawBass.transition X)) :=
  (Homotopy.precomp (evaluation Y) (GlobalRawBass.transitionInputHomotopy g)).trans
    (((evaluationComparison g).symm.postcomp (GlobalRawBass.transition X)).cast
      (Category.assoc _ _ _) (Category.assoc _ _ _))

/-- The two original evaluation/input composites are homotopic after the actual initial seed.
This restricted comparison does not assert naturality on the whole raw first stage. -/
def inputSeedHomotopy :
    Homotopy ((strictSeed Y ≫ stepEvaluation Y) ≫ GlobalRawBass.map g)
      (sectionMap g ≫ (strictSeed X ≫ stepEvaluation X)) :=
  ((inputSeedEvaluationTrack g).trans (inputSeedRawTrack g)).trans
    (Homotopy.precomp (sectionMap g) (seedHomotopy X).symm)

/-- The restricted comparison retains its independent output-loop and spectrum coordinates. -/
theorem inputSeedHomotopy_structure (n : ℕ) (r s t : unitInterval)
    (x : (GlobalSchemeLaurentTrack.diagram.obj (op Y)).space n) :
    Path.toContinuousMap ((inputSeedHomotopy g).level (n + 1)
      (r, (GlobalSchemeLaurentTrack.diagram.obj (op Y)).structureMap n x t)) s =
      Path.toContinuousMap ((GlobalRawBass.step X).structureMap n
        ((inputSeedHomotopy g).level n (r, x)) t) s :=
  congrArg (fun p => Path.toContinuousMap p s) ((inputSeedHomotopy g).comm n r x t)

end Quillen.PerfectComplexes.GlobalBassEvaluation
