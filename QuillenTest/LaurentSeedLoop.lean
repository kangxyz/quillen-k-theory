/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.LaurentSeedLoop

/-! Regression tests for the original Laurent seed word and its two loop coordinates. -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open Quillen.KTheory.Bass Quillen.KTheory.Bass.LaurentSeed
open scoped unitInterval
universe u w
namespace QuillenTest.LaurentSeedLoop
variable {R : CommRingCat.{u}} {F : Under R ⥤ LoopPrespectrum.{w}}

/-- Loop strength retains the full original reversed-null/action/null concatenation. -/
theorem original_word (A : Track F) (a : Under R) (n : ℕ)
    (γ : Path ((F.obj a).point n) ((F.obj a).point n)) (r t : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      ((A.loop.seedMap a ≫ LoopStrength.strength
        (laurentUnderSquareFunctor R) F a).map n γ) r) t =
      (((A.homotopy a).postcomp (mappingConeInclusion (StrictSquare.comparison (square F a))))
        |>.conjugateToZero (sourceNull F a)).level n (t, γ r) :=
  (A.seed_loop_strength_apply a n γ r t).trans (A.seedMap_apply a n (γ r) t)

/-- Transposition changes only the order of the input-loop and original seed coordinates. -/
theorem transpose_coordinates (A : Track F) (a : Under R) (n : ℕ)
    (γ : Path ((F.obj a).point n) ((F.obj a).point n)) (r t : unitInterval) :
    doubleLoopTranspose ((cone F a).point n)
      ((A.loop.seedMap a ≫ LoopStrength.strength
        (laurentUnderSquareFunctor R) F a).map n γ) t r =
      Path.toContinuousMap ((A.seedMap a).map n (γ r)) t := by
  exact A.seed_loop_strength_apply a n γ r t

#print axioms Quillen.KTheory.Bass.LaurentSeed.Track.loop
#print axioms Quillen.KTheory.Bass.LaurentSeed.Track.seed_loop_strength
#print axioms QuillenTest.LaurentSeedLoop.original_word
#print axioms QuillenTest.LaurentSeedLoop.transpose_coordinates

end QuillenTest.LaurentSeedLoop
