/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedRoutes
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenMappedRelativeExtension

/-!
# The prescribed original evaluation seed comparison for a scheme arrow

Both complete chosen route surfaces have actual carrier lifts with all whole edges proved.
The finite two-tip carrier extension gives a relative comparison of their original native
images, preserving every route, comparison, seed, and prespectrum structure coordinate.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedNaturality
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedCarrier
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The two complete prescribed native routes are exactly the two proved outer carrier faces. -/
theorem recovers : (InputSeedRoutes.surfaces g).boundary.RecoversMappedRoutes
    (GlobalRawBass.InputIdentityPositive.inclusion X)
    (InputSeedWords.longRoute g) (InputSeedWords.shortRoute g) where
  left z n x := InputSeedRoutes.long_native g n (z.val.val 1) (z.val.val 2) x
  right z n x := InputSeedRoutes.short_native g n (z.val.val 1) (z.val.val 2) x

/-- The actual original three-piece and two-piece seed routes are homotopic relative endpoints. -/
def comparison : (InputSeedWords.longRoute g).RelHomotopy (InputSeedWords.shortRoute g) :=
  (InputSeedRoutes.surfaces g).boundary.mappedRelativeComparison
    (GlobalRawBass.InputIdentityPositive.inclusion X)
    (InputSeedWords.longRoute g) (InputSeedWords.shortRoute g) (recovers g)

/-- All three independent comparison, route and seed times retain the actual carrier extension. -/
theorem comparison_apply (n : ℕ) (r s t : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((comparison g).level n (r, (s, x))) t =
      (GlobalRawBass.InputIdentityPositive.inclusion X).map n
        (CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
          (ordinary g) (shifted g) n
          ((InputSeedRoutes.surfaces g).boundary.carrier ((r, s), t)) x) :=
  (InputSeedRoutes.surfaces g).boundary.mappedRelativeComparison_apply
    (GlobalRawBass.InputIdentityPositive.inclusion X)
    (InputSeedWords.longRoute g) (InputSeedWords.shortRoute g) (recovers g) n r s t x

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedNaturality
