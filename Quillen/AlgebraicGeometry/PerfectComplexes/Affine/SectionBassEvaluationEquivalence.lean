/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassEvaluation
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassEvaluationTopology
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionSpectrumEquivalence
public import Quillen.Topology.Prespectrum.PushoutHomotopySquareEquivalence
public import Quillen.Topology.Prespectrum.ConeSquareLevelWeakEquivalence
public import Quillen.Topology.Prespectrum.ParameterLoopingWeakEquivalence

/-!
# Genuine weak and stable equivalence of the original one-step Bass evaluation

The actual polynomial and Laurent evaluation maps are complete weak equivalences at every
level. Original point HEP and the proved whole evaluation filler therefore preserve the original
span, cone and parameter-looped step. The target is the unchanged raw bounded-flat construction,
whose coefficient maps remain homotopy-natural. No strict target diagram or seed compatibility
is assumed, and no new stable-excision hypothesis is introduced.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.Scheme.PolynomialLaurent Quillen.PolynomialBaseChange
universe u
namespace Quillen.PerfectComplexes
variable (R : CommRingCat.{u})

/-- The unchanged whole-track polynomial-span evaluation is completely weak at every level. -/
theorem boundedFlatAffineSectionBassSpanEvaluation_level_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedFlatAffineSectionBassSpanEvaluation R).map n) :=
  HomotopyPushout.mapOfHomotopies_level_isWeakHomotopyEquivalence
    (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
    (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatAffineSectionEvaluationPrespectrumMap R)
    (boundedFlatAffineSectionEvaluationPrespectrumMap (.of (Polynomial R)))
    (boundedFlatAffineSectionEvaluationPrespectrumMap (.of (Polynomial R)))
    (boundedFlatAffineSectionEvaluationCoefficientHomotopy (coefficient R))
    (boundedFlatAffineSectionEvaluationCoefficientHomotopy (coefficient R)) n
    (prespectrum_point_homotopyExtensionProperty (boundedFlatAffineSectionModel R) n)
    (prespectrum_point_homotopyExtensionProperty
      (boundedFlatAffineSectionModel (.of (Polynomial R))) n)
    (prespectrum_point_homotopyExtensionProperty
      (boundedFlatAffineSectionModel (.of (Polynomial R))) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (Spec R)) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (Spec (.of (Polynomial R)))) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (Spec (.of (Polynomial R)))) n)
    (boundedFlatAffineSectionEvaluation_level_isWeakHomotopyEquivalence R n)
    (boundedFlatAffineSectionEvaluation_level_isWeakHomotopyEquivalence (.of (Polynomial R)) n)
    (boundedFlatAffineSectionEvaluation_level_isWeakHomotopyEquivalence (.of (Polynomial R)) n)

/-- The original actual span evaluation is stable in every signed degree. -/
theorem boundedFlatAffineSectionBassSpanEvaluation_isStableEquivalence :
    IsStableEquivalence (boundedFlatAffineSectionBassSpanEvaluation R) :=
  isStableEquivalence_of_levelwise _
    (boundedFlatAffineSectionBassSpanEvaluation_level_isWeakHomotopyEquivalence R)

/-- The exact cone map with the proved original filler is completely weak at every level. -/
theorem boundedFlatAffineSectionBassConeEvaluation_level_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedFlatAffineSectionBassConeEvaluation R).map n) :=
  mappingConeSquareMap_level_isWeakHomotopyEquivalence
    (StrictSquare.comparison (boundedFlatAffineSectionBassSquare R))
    (boundedFlatBassSquareComparison R) (boundedFlatAffineSectionBassSpanEvaluation R)
    (boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
    (boundedFlatAffineSectionBassComparisonEvaluationHomotopy R) n
    (boundedFlatAffineSectionBassSpan_point_homotopyExtensionProperty R n)
    (prespectrum_point_homotopyExtensionProperty
      (boundedFlatAffineSectionModel (.of (LaurentPolynomial R))) n)
    (boundedFlatBassSpan_point_homotopyExtensionProperty R n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R)))) n)
    (boundedFlatAffineSectionBassSpanEvaluation_level_isWeakHomotopyEquivalence R n)
    (boundedFlatAffineSectionEvaluation_level_isWeakHomotopyEquivalence
      (.of (LaurentPolynomial R)) n)

/-- The unchanged original cone evaluation is a genuine signed stable equivalence. -/
theorem boundedFlatAffineSectionBassConeEvaluation_isStableEquivalence :
    IsStableEquivalence (boundedFlatAffineSectionBassConeEvaluation R) :=
  isStableEquivalence_of_levelwise _
    (boundedFlatAffineSectionBassConeEvaluation_level_isWeakHomotopyEquivalence R)

/-- Actual parameter looping preserves every component at every original level, including zero. -/
theorem boundedFlatAffineSectionBassStepEvaluation_level_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedFlatAffineSectionBassStepEvaluation R).map n) :=
  basedLoopMap_isWeakHomotopyEquivalence
    ((boundedFlatAffineSectionBassConeEvaluation R).map n)
    ((boundedFlatAffineSectionBassConeEvaluation R).map_point n)
    (boundedFlatAffineSectionBassConeEvaluation_level_isWeakHomotopyEquivalence R n)

/-- The original strict-section Bass stage maps stably to the unchanged raw geometric Bass step. -/
theorem boundedFlatAffineSectionBassStepEvaluation_isStableEquivalence :
    IsStableEquivalence (boundedFlatAffineSectionBassStepEvaluation R) :=
  isStableEquivalence_of_levelwise _
    (boundedFlatAffineSectionBassStepEvaluation_level_isWeakHomotopyEquivalence R)

end Quillen.PerfectComplexes
