/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterCoefficientSeedCompatibility

/-! # Actual Spec seed comparison at every original output-loop coordinate -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.PerfectComplexes
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.GlobalParameterCoefficient
universe u
namespace QuillenTest.GlobalParameterCoefficientSeed

/-- The actual comparison retains each independent output-loop time. -/
theorem seed_at (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ) (t : unitInterval)
    (x : ((parameterDiagram Q).obj (specUnder.obj a)).space n) :
    Path.toContinuousMap (((bassComparison Q).app a).map n
      (((SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q.left)).app
        (specUnder.obj a)).map n x)) t =
      Path.toContinuousMap (((globalLaurentAction Q).track.seed.app a).map n
        (((rowComparison Q).app a).map n x)) t := by
  exact congrArg (fun η => Path.toContinuousMap ((η.app a).map n x) t) (seed_square Q)

#print axioms seed_at
end QuillenTest.GlobalParameterCoefficientSeed
