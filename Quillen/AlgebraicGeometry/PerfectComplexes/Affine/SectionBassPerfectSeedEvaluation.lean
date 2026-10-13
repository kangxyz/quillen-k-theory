/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassSeedEvaluation
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassTransitionInclusion

/-!
# Original perfect Bass seed evaluation

The original strict section seed is compared with the original perfect Bass transition through
the actual one-step evaluation and bounded-flat inclusion maps. This is a single seed square.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The actual strict seed square followed by the original bounded-flat/perfect seed square. -/
def boundedFlatAffineSectionPerfectBassSeedEvaluationHomotopy (R : CommRingCat.{u}) :
    Homotopy
      (boundedFlatAffineSectionBassSeedMap R ≫
        (boundedFlatAffineSectionBassStepEvaluation R ≫
          boundedFlatPerfectGeometricBassStepMap R))
      ((boundedFlatAffineSectionEvaluationPrespectrumMap R ≫
        exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec R))
          (perfectWaldhausen (Spec R)) (boundedFlatPerfectInclusion_exact _)) ≫
        affineBassTransition R) :=
  (((boundedFlatAffineSectionBassSeedEvaluationHomotopy R).postcomp
    (boundedFlatPerfectGeometricBassStepMap R)).cast (Category.assoc _ _ _)
      (Category.assoc _ _ _)).trans
    ((Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
      (boundedFlatPerfectBassTransitionHomotopy R)).cast rfl (Category.assoc _ _ _).symm)

end Quillen.PerfectComplexes
