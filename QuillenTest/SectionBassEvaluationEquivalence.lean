/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassEvaluationEquivalence
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassGeometricComparison

/-!
# Original one-step Bass evaluation equivalence consumers

The actual raw target, original whole filler and parameter-loop map are retained. Consumers
verify negative signed groups, actual component coverage including the zero-level span, literal
cone inclusion and loop time, plus composition with the unchanged original perfect comparison.
No compatibility with the original seed transition is inferred here.
-/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.PolynomialLaurent
open scoped unitInterval
universe u
namespace QuillenTest.SectionBassEvaluationEquivalence

open Quillen
variable (R : CommRingCat.{u})

/-- The unchanged section-to-raw step map is invertible in every original negative stable degree. -/
theorem original_raw_step_negative_iso (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      (boundedFlatAffineSectionBassStepEvaluation R)) :=
  boundedFlatAffineSectionBassStepEvaluation_isStableEquivalence R _

/-- Every actual raw loop component is reached, including original level zero. -/
theorem original_raw_step_component_coverage (n : ℕ)
    (y : (boundedFlatAffineBassStep R).space n) :
    ∃ x : ((boundedFlatAffineSectionBassDiagram 1).obj R).space n,
      Joined ((boundedFlatAffineSectionBassStepEvaluation R).map n x) y :=
  (boundedFlatAffineSectionBassStepEvaluation_level_isWeakHomotopyEquivalence
    R n).component_surjective y

/-- The actual degree-zero raw span also has complete component coverage. -/
theorem original_raw_span_zero_component_coverage
    (y : (HomotopyPushout.prespectrum
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))).space 0) :
    ∃ x : (StrictSquare.span (boundedFlatAffineSectionBassSquare R)).space 0,
      Joined ((boundedFlatAffineSectionBassSpanEvaluation R).map 0 x) y :=
  (boundedFlatAffineSectionBassSpanEvaluation_level_isWeakHomotopyEquivalence
    R 0).component_surjective y

/-- The original Laurent evaluation is retained on the actual target-cone inclusion. -/
theorem original_cone_inclusion :
    mappingConeInclusion (StrictSquare.comparison (boundedFlatAffineSectionBassSquare R)) ≫
        boundedFlatAffineSectionBassConeEvaluation R =
      boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)) ≫
        mappingConeInclusion (boundedFlatBassSquareComparison R) :=
  mappingConeSquareMap_inclusion _ _ _ _
    (boundedFlatAffineSectionBassComparisonEvaluationHomotopy R)

/-- The original loop parameter remains independent of the cone/filler cylinder coordinates. -/
theorem original_step_loop_value (n : ℕ)
    (p : Path ((boundedFlatAffineSectionBassCone R).point n)
      ((boundedFlatAffineSectionBassCone R).point n)) (t : unitInterval) :
    Path.toContinuousMap (show Path _ _ from
      (boundedFlatAffineSectionBassStepEvaluation R).map n p) t =
        (boundedFlatAffineSectionBassConeEvaluation R).map n (p t) := rfl

/-- The literal original raw loop point at level zero has genuine HEP. -/
theorem original_raw_loop_zero_point_hep :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((boundedFlatAffineBassStep R).point 0))) :=
  boundedFlatAffineBassStep_point_homotopyExtensionProperty R 0

/-- Composition with the original bounded-flat/perfect step preserves signed stable groups. -/
theorem original_perfect_step_composite_signed_iso (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map
      (boundedFlatAffineSectionBassStepEvaluation R ≫ boundedFlatPerfectGeometricBassStepMap R)) :=
  (boundedFlatAffineSectionBassStepEvaluation_isStableEquivalence R).comp
    (boundedFlatPerfectGeometricBassStepMap_isStableEquivalence R) d

end QuillenTest.SectionBassEvaluationEquivalence
