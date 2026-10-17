/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedPushoutComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSecondCoefficientProjection
public import Quillen.Topology.Prespectrum.HomotopySquareComposition

/-! Literal composite-span reductions for naturality of the actual first seed.
The higher leg square is separate from these unconditional whole-map homotopies. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedSpanNaturality
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- The left composite retains its two original leg tracks and half clock. -/
def leftTrack := HomotopyPushout.identicalLegPastedTrack
  (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
  (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app b))
  (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
  (boundedFlatCoefficientBassTransition P b)
  (boundedFlatCoefficientBassTransition P ((polynomialUnderFunctor R).obj b))
  (boundedFlatCoefficientPolynomialSquareHomotopy P u)
  (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
    ((polynomialUnderCoefficient R).app b)).symm

/-- The right composite retains its two original leg tracks and half clock. -/
def rightTrack := HomotopyPushout.identicalLegPastedTrack
  (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app b))
  (boundedFlatCoefficientBassTransition P a)
  (boundedFlatCoefficientBassTransition P ((polynomialUnderFunctor R).obj a))
  (boundedFlatCoefficientBassStepMap P u)
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderFunctor R).map u))
  (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
    ((polynomialUnderCoefficient R).app a)).symm
  (CoefficientBassSecondCoefficientProjection.polynomialSquare P u)

/-- The left composite span with its literal pasted leg track. -/
def leftSpan := HomotopyPushout.mapOfHomotopies
  (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
  (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app b))
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app b))
  (boundedFlatPerfectPrespectrumMap (coefficientMap P u) ≫
      boundedFlatCoefficientBassTransition P b)
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
      boundedFlatCoefficientBassTransition P ((polynomialUnderFunctor R).obj b))
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
      boundedFlatCoefficientBassTransition P ((polynomialUnderFunctor R).obj b))
  (leftTrack P u) (leftTrack P u)

/-- The right composite span with its literal pasted leg track. -/
def rightSpan := HomotopyPushout.mapOfHomotopies
  (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
  (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app b))
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app b))
  (boundedFlatCoefficientBassTransition P a ≫ boundedFlatCoefficientBassStepMap P u)
  (boundedFlatCoefficientBassTransition P ((polynomialUnderFunctor R).obj a) ≫
      boundedFlatCoefficientBassStepMap P ((polynomialUnderFunctor R).map u))
  (boundedFlatCoefficientBassTransition P ((polynomialUnderFunctor R).obj a) ≫
      boundedFlatCoefficientBassStepMap P ((polynomialUnderFunctor R).map u))
  (rightTrack P u) (rightTrack P u)

/-- The first original map composite is homotopic to its exact pasted-span presentation. -/
def leftReduction : Homotopy
    (boundedFlatCoefficientPolynomialSpanMap P u ≫ CoefficientBassSeedPushoutComparison.spanMap P b)
    (leftSpan P u) :=
  HomotopyPushout.identicalLegCompositionHomotopy
  (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
  (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app b))
  (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
  (boundedFlatCoefficientBassTransition P b)
  (boundedFlatCoefficientBassTransition P ((polynomialUnderFunctor R).obj b))
  (boundedFlatCoefficientPolynomialSquareHomotopy P u)
  (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
    ((polynomialUnderCoefficient R).app b)).symm

/-- The second original map composite is homotopic to its exact pasted-span presentation. -/
def rightReduction : Homotopy
    (CoefficientBassSeedPushoutComparison.spanMap P a ≫
      CoefficientBassSecondCoefficientProjection.spanMap P u)
    (rightSpan P u) :=
  HomotopyPushout.identicalLegCompositionHomotopy
  (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app b))
  (boundedFlatCoefficientBassTransition P a)
  (boundedFlatCoefficientBassTransition P ((polynomialUnderFunctor R).obj a))
  (boundedFlatCoefficientBassStepMap P u)
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderFunctor R).map u))
  (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
    ((polynomialUnderCoefficient R).app a)).symm
  (CoefficientBassSecondCoefficientProjection.polynomialSquare P u)

end Quillen.PerfectComplexes.CoefficientBassSeedSpanNaturality
