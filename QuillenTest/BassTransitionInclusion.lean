/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassTransitionInclusion

/-!
Original transition composites, literal loop coordinates and the signed stable transition square.
-/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.BassTransitionInclusion

open Quillen
variable (R : CommRingCat.{u})

/-- The initial map is exactly the original transition followed by the geometric comparison step. -/
theorem original_source :
    (boundedFlatPerfectBassTransitionHomotopy R).at 0 =
      boundedFlatAffineBassTransition R ≫ boundedFlatPerfectGeometricBassStepMap R :=
  Homotopy.at_zero_eq _

/-- The final map is exactly original base inclusion followed by the perfect transition. -/
theorem original_target :
    (boundedFlatPerfectBassTransitionHomotopy R).at 1 =
      exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec R))
        (perfectWaldhausen (Spec R)) (boundedFlatPerfectInclusion_exact _) ≫
        affineBassTransition R :=
  Homotopy.at_one_eq _

/-- Every loop coordinate is the original proved null-loop conjugation comparison. -/
theorem original_loop (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    Path.toContinuousMap
      ((boundedFlatPerfectBassTransitionHomotopy R).level n (r, x)) s =
      (BassInclusionTransitionTrack.conjugateComparison R).level n (r, (s, x)) :=
  boundedFlatPerfectBassTransitionHomotopy_apply R n r s x

/-- The original degree-zero based-loop level is included in the full comparison. -/
theorem degree_zero_loop (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space 0) :
    Path.toContinuousMap
      ((boundedFlatPerfectBassTransitionHomotopy R).level 0 (r, x)) s =
      (BassInclusionTransitionTrack.conjugateComparison R).level 0 (r, (s, x)) :=
  boundedFlatPerfectBassTransitionHomotopy_apply R 0 r s x

/-- Comparison, loop evaluation and original structure times are independently preserved. -/
theorem three_parameters (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    Path.toContinuousMap ((boundedFlatPerfectBassTransitionHomotopy R).level (n + 1)
      (r, (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).structureMap n x t)) s =
    Path.toContinuousMap ((affineBassStep R).structureMap n
      ((boundedFlatPerfectBassTransitionHomotopy R).level n (r, x)) t) s :=
  congrArg (fun p ↦ Path.toContinuousMap p s)
    ((boundedFlatPerfectBassTransitionHomotopy R).comm n r x t)

/-- The two unchanged original transition composites agree in every signed stable degree. -/
theorem signed_stable_transition_square (q : ℤ) :
    (stableHomotopyFunctor q).map (boundedFlatAffineBassTransition R) ≫
        (stableHomotopyFunctor q).map (boundedFlatPerfectGeometricBassStepMap R) =
      (stableHomotopyFunctor q).map (exactOriginalPrespectrumMap
        (boundedFlatPerfectWaldhausen (Spec R)) (perfectWaldhausen (Spec R))
        (boundedFlatPerfectInclusion_exact _)) ≫
        (stableHomotopyFunctor q).map (affineBassTransition R) := by
  simpa only [Functor.map_comp] using
    (boundedFlatPerfectBassTransitionHomotopy R).stableHomotopyMap_eq q

end QuillenTest.BassTransitionInclusion
