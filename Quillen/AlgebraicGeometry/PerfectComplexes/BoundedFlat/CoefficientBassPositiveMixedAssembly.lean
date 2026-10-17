/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveMixedRoutes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierSeed
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenRelativeExtension
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels

/-! Conditional final assembly for the exact original positive mixed routes.
The still-required input is the six actual carrier boundary faces, their full edge matches and
whole native route recovery. No relative filler is supplied as a hypothesis.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveMixedAssembly
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierAttachment CoefficientBassPositiveMixedRoutes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The six boundary faces live in the actual fixed polynomial/Laurent two-tip carrier. -/
abbrev Boundary :=
  CutOpenCarrier.RelativeBoundary
    (polynomialReference P ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a))
    (chartMap P (c := (laurentUnderFunctor R).obj a))
    (laurentReference P ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a))
    (ordinaryAnchor P ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a))
    (LaurentUnitReferenceSpecialization.shiftedAnchor P
      ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a))

/-- Exact whole supported-route recovery is a remaining boundary obligation, at every native
level and both independent route/seed coordinates. It does not assert the desired filler. -/
abbrev RecoversSupportedRoutes (B : Boundary P a) :=
  B.RecoversRoutes (supportedLeft P a) (supportedRight P a)

/-- Fill the actual compatible boundary and evaluate it to obtain the required supported
relative comparison. This declaration is conditional on the named boundary obligations. -/
def supportedComparison (B : Boundary P a) (h : RecoversSupportedRoutes P a B) :
    (supportedLeft P a).RelHomotopy (supportedRight P a) :=
  B.relativeComparison (supportedLeft P a) (supportedRight P a) h

/-- The literal strict positive inclusion carries the assembled comparison to the two
original mixed routes, retaining all comparison, route and output-loop coordinates. -/
def originalComparison (B : Boundary P a) (h : RecoversSupportedRoutes P a B) :
    (originalLeft P a).RelHomotopy (originalRight P a) := by
  let inclusion := parameterLoopingMap
    (boundedFlatCoefficientBassPositiveConeInclusion P ((laurentUnderFunctor R).obj a))
  let J := (supportedComparison P a B h).postcomp inclusion
  apply J.ofLevels (originalLeft P a) (originalRight P a)
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    exact (supportedLeft_mapped P a n x r).symm
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    exact (supportedRight_mapped P a n x r).symm

end Quillen.PerfectComplexes.CoefficientBassPositiveMixedAssembly
