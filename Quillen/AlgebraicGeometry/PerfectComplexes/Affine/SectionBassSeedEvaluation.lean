/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassEvaluationNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionLaurentEvaluationHomotopy
public import Quillen.Topology.Prespectrum.RelativeHomotopyConjugation
public import Quillen.Topology.Prespectrum.RelativeHomotopyLoop

/-!
# Original strict and raw Bass seed evaluation

The original conjugated loops retain the actual Laurent-unit action and nullhomotopies.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.PolynomialBaseChange Quillen.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.SectionBassSeedEvaluation
variable (R : CommRingCat.{u})

/-- The original strict section unit followed by Laurent evaluation and raw cone inclusion. -/
def oldUnit :=
  ((boundedFlatAffineSectionLaurentUnitHomotopy R).postcomp
    (boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)))).postcomp
      (mappingConeInclusion (boundedFlatBassSquareComparison R))

/-- The original raw Laurent-unit loop between base evaluation and cone inclusion. -/
def newUnit :=
  (Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
    (boundedFlatLaurentUnitHomotopy R)).postcomp
      (mappingConeInclusion (boundedFlatBassSquareComparison R))

/-- The genuine original unit comparison retains its entire raw-cone image. -/
def unitPasting :
    ((oldUnit R).trans (SectionBassEvaluationNull.laurentMovement R)).RelHomotopy
      ((SectionBassEvaluationNull.laurentMovement R).trans (newUnit R)) := by
  simpa only [Homotopy.postcomp_trans, oldUnit, newUnit,
    SectionBassEvaluationNull.laurentMovement,
    boundedFlatAffineSectionLaurentEvaluationOldUnit,
    boundedFlatAffineSectionLaurentEvaluationNewUnit] using
    (boundedFlatAffineSectionLaurentEvaluationUnitPasting R).postcomp
      (mappingConeInclusion (boundedFlatBassSquareComparison R))

/-- Both proved original comparisons identify the complete based conjugated loops. -/
def conjugateComparison :=
  Homotopy.RelHomotopy.conjugateNaturality (SectionBassEvaluationNull.laurentMovement R)
    (oldUnit R) (newUnit R) (SectionBassEvaluationNull.originalOldNull R)
    (SectionBassEvaluationNull.originalNewNull R) (unitPasting R)
    (SectionBassEvaluationNull.originalNullComparison R)

/-- The source loop map is exactly the strict seed followed by the proved Bass evaluation map. -/
theorem source_eq :
    ((oldUnit R).conjugateToZero (SectionBassEvaluationNull.originalOldNull R)).zeroLoopMap =
      boundedFlatAffineSectionBassSeedMap R ≫ boundedFlatAffineSectionBassStepEvaluation R := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change ((oldUnit R).conjugateToZero (SectionBassEvaluationNull.originalOldNull R)).level n
    (s, x) =
    ((((boundedFlatAffineSectionLaurentUnitHomotopy R).postcomp
      (mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineSectionBassSquare R)))).conjugateToZero
        (boundedFlatAffineSectionBassNullHomotopy R)).postcomp
          (boundedFlatAffineSectionBassConeEvaluation R)).level n (s, x)
  simp only [Homotopy.conjugateToZero, Homotopy.postcomp_trans, Homotopy.postcomp_symm]
  rfl

/-- The target loop map is exactly original base evaluation followed by the raw transition. -/
theorem target_eq :
    ((newUnit R).conjugateToZero (SectionBassEvaluationNull.originalNewNull R)).zeroLoopMap =
      boundedFlatAffineSectionEvaluationPrespectrumMap R ≫
        boundedFlatAffineBassTransition R := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change ((newUnit R).conjugateToZero (SectionBassEvaluationNull.originalNewNull R)).level n
    (s, x) =
    (Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
      (((boundedFlatLaurentUnitHomotopy R).postcomp
        (mappingConeInclusion (boundedFlatBassSquareComparison R))).conjugateToZero
          (boundedFlatBassLaurentNullHomotopy R))).level n (s, x)
  simp only [Homotopy.conjugateToZero, Homotopy.precomp_trans, Homotopy.precomp_symm]
  rfl


end Quillen.PerfectComplexes.SectionBassSeedEvaluation

namespace Quillen.PerfectComplexes

/-- Original strict seed evaluation agrees through a genuine whole homotopy with the raw
geometric Bass transition, using the original Laurent unit and both original null tracks. -/
def boundedFlatAffineSectionBassSeedEvaluationHomotopy (R : CommRingCat.{u}) :
    Homotopy
      (boundedFlatAffineSectionBassSeedMap R ≫ boundedFlatAffineSectionBassStepEvaluation R)
      (boundedFlatAffineSectionEvaluationPrespectrumMap R ≫ boundedFlatAffineBassTransition R) :=
  (SectionBassSeedEvaluation.conjugateComparison R).zeroLoopMapHomotopy.cast
    (SectionBassSeedEvaluation.source_eq R) (SectionBassSeedEvaluation.target_eq R)

end Quillen.PerfectComplexes
