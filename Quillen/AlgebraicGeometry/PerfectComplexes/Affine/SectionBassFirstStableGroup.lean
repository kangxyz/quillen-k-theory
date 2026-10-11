/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassFirstStableGroup
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassEvaluationEquivalence

/-!
# The unchanged strict first Bass stage in degree minus one

The proved actual one-step evaluation map transports the original first Bass cokernel to the
strict section first stage. Its signed stable map, rather than a replacement equivalence, is
retained in the comparison equation. Later-stage stabilization is a separate question.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- The original perfect-K-zero Bass cokernel computes the strict first Bass stage. -/
def boundedFlatAffineSectionBassFirstStableGroupIso (R : CommRingCat.{u}) :
    Quillen.Bass.negativeK R 1 ≅
      stableHomotopyGroup ((boundedFlatAffineSectionBassDiagram 1).obj R) (-1) := by
  let := boundedFlatAffineSectionBassStepEvaluation_isStableEquivalence R (-1)
  exact boundedFlatBassFirstStableGroupIso R ≪≫
    (asIso ((stableHomotopyFunctor (-1)).map
      (boundedFlatAffineSectionBassStepEvaluation R))).symm

/-- The original one-step evaluation map recovers the unchanged raw first-step comparison. -/
@[reassoc]
theorem boundedFlatAffineSectionBassFirstStableGroupIso_evaluation (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionBassFirstStableGroupIso R).hom ≫
      (stableHomotopyFunctor (-1)).map (boundedFlatAffineSectionBassStepEvaluation R) =
    (boundedFlatBassFirstStableGroupIso R).hom := by
  let := boundedFlatAffineSectionBassStepEvaluation_isStableEquivalence R (-1)
  simp [boundedFlatAffineSectionBassFirstStableGroupIso]

/-- Original Laurent classes retain the actual raw cone-inclusion formula after evaluation. -/
@[reassoc]
theorem boundedFlatAffineSectionBassFirstStableGroupIso_π_evaluation (R : CommRingCat.{u}) :
    Quillen.Bass.negativeKπ R 0 ≫ (boundedFlatAffineSectionBassFirstStableGroupIso R).hom ≫
      (stableHomotopyFunctor (-1)).map (boundedFlatAffineSectionBassStepEvaluation R) =
    boundedFlatBassFirstLaurentMap R := by
  rw [boundedFlatAffineSectionBassFirstStableGroupIso_evaluation,
    boundedFlatBassFirstStableGroupIso_π]

end Quillen.PerfectComplexes
