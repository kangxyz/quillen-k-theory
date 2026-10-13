/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassTransitionNaturality

/-! Literal transition composites and all independent coordinates for arbitrary coefficient maps. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.BassTransitionCoefficientNaturality

open Quillen
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The initial map is exactly the original transition followed by the genuine coefficient step. -/
theorem original_source :
    (boundedFlatAffineBassTransitionCoefficientHomotopy f).at 0 =
      boundedFlatAffineBassTransition R ≫ boundedFlatAffineBassStepMap f :=
  Homotopy.at_zero_eq _

/-- The final map is exactly original geometric base pullback followed by the new transition. -/
theorem original_target :
    (boundedFlatAffineBassTransitionCoefficientHomotopy f).at 1 =
      boundedFlatPerfectPrespectrumMap (Spec.map f) ≫ boundedFlatAffineBassTransition S :=
  Homotopy.at_one_eq _

/-- Every loop coordinate is the original proved null-loop conjugation comparison. -/
theorem original_loop (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    Path.toContinuousMap
      ((boundedFlatAffineBassTransitionCoefficientHomotopy f).level n (r, x)) s =
      (BassTransitionTrack.conjugateComparison f).level n (r, (s, x)) :=
  boundedFlatAffineBassTransitionCoefficientHomotopy_apply f n r s x

/-- The original degree-zero based-loop level is included in the full comparison. -/
theorem degree_zero_loop (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space 0) :
    Path.toContinuousMap
      ((boundedFlatAffineBassTransitionCoefficientHomotopy f).level 0 (r, x)) s =
      (BassTransitionTrack.conjugateComparison f).level 0 (r, (s, x)) :=
  boundedFlatAffineBassTransitionCoefficientHomotopy_apply f 0 r s x

/-- Comparison, loop evaluation and original structure times are independently preserved. -/
theorem three_parameters (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    Path.toContinuousMap ((boundedFlatAffineBassTransitionCoefficientHomotopy f).level (n + 1)
      (r, (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).structureMap n x t)) s =
    Path.toContinuousMap ((boundedFlatAffineBassStep S).structureMap n
      ((boundedFlatAffineBassTransitionCoefficientHomotopy f).level n (r, x)) t) s :=
  congrArg (fun p ↦ Path.toContinuousMap p s)
    ((boundedFlatAffineBassTransitionCoefficientHomotopy f).comm n r x t)

end QuillenTest.BassTransitionCoefficientNaturality
