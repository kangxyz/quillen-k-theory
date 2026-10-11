/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassPerfectSeedEvaluation

/-! Consumers retain both original perfect seed endpoints and the independent structure time. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes
open scoped unitInterval
universe u
namespace Quillen.Tests.SectionBassPerfectSeedEvaluation

/-- The source is the original strict seed followed by both original comparison maps. -/
theorem original_source (R : CommRingCat.{u}) (n : ℕ)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionPerfectBassSeedEvaluationHomotopy R).level n (0, x) =
      (boundedFlatAffineSectionBassSeedMap R ≫
        (boundedFlatAffineSectionBassStepEvaluation R ≫
          boundedFlatPerfectGeometricBassStepMap R)).map n x :=
  (boundedFlatAffineSectionPerfectBassSeedEvaluationHomotopy R).at_zero n x

/-- The target is original evaluation and inclusion followed by the original perfect transition. -/
theorem original_target (R : CommRingCat.{u}) (n : ℕ)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionPerfectBassSeedEvaluationHomotopy R).level n (1, x) =
      ((boundedFlatAffineSectionEvaluationPrespectrumMap R ≫
        exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec R))
          (perfectWaldhausen (Spec R)) (boundedFlatPerfectInclusion_exact _)) ≫
        affineBassTransition R).map n x :=
  (boundedFlatAffineSectionPerfectBassSeedEvaluationHomotopy R).at_one n x

/-- The original perfect seed comparison retains its independent structure parameter. -/
theorem structure_time (R : CommRingCat.{u}) (n : ℕ) (r t : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionPerfectBassSeedEvaluationHomotopy R).level (n + 1)
      (r, (boundedFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t) =
      (affineBassStep R).structureMap n
        ((boundedFlatAffineSectionPerfectBassSeedEvaluationHomotopy R).level n (r, x)) t :=
  (boundedFlatAffineSectionPerfectBassSeedEvaluationHomotopy R).comm n r x t

end Quillen.Tests.SectionBassPerfectSeedEvaluation
