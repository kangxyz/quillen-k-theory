/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeActualRightRoute
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveMixedAssembly
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenSurfaceBoundary

/-! Assemble the actual original negative mixed filler from the two proved carrier routes. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassNegativeActualMixedFiller
open CommonReferenceNerve CoefficientBassNegativeActualLeftRoute
open CoefficientBassNegativeMixedRoutes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- Both actual continuous routes share whole endpoint paths and retain the two separate tips. -/
def surfaces : CutOpenCarrier.RouteSurfaces (polyRef P d) (chart P d) (laurentRef P d)
    (ordinary P d) (shifted P d) where
  left := CoefficientBassNegativeActualLeftRoute.route P d
  right := CoefficientBassNegativeActualRightRoute.route P d
  start := CoefficientBassNegativeActualLeftRoute.start P d
  finish := CoefficientBassNegativeActualLeftRoute.finish P d
  left_start := CoefficientBassNegativeActualLeftRoute.route_start P d
  left_finish := CoefficientBassNegativeActualLeftRoute.route_finish P d
  right_start := CoefficientBassNegativeActualRightRoute.route_start P d
  right_finish := CoefficientBassNegativeActualRightRoute.route_finish P d
  left_zero := CoefficientBassNegativeActualLeftRoute.route_bottom P d
  left_one := CoefficientBassNegativeActualLeftRoute.route_top P d
  right_zero := CoefficientBassNegativeActualRightRoute.route_bottom P d
  right_one := CoefficientBassNegativeActualRightRoute.route_top P d

/-- The complete six-face boundary is derived from the actual routes and their proved edges. -/
def boundary := (surfaces P d).boundary

/-- Whole native route recovery uses the actual two comparison surfaces at every degree. -/
theorem recovers : (boundary P d).RecoversRoutes (supportedLeft P d) (supportedRight P d) :=
  (surfaces P d).recoversRoutes (supportedLeft P d) (supportedRight P d)
    (CoefficientBassNegativeActualLeftRoute.route_native P d)
    (CoefficientBassNegativeActualRightRoute.route_native P d)

/-- The exact original supported negative mixed comparison, with no boundary premise. -/
def supportedComparison : (supportedLeft P d).RelHomotopy (supportedRight P d) :=
  (boundary P d).relativeComparison (supportedLeft P d) (supportedRight P d) (recovers P d)

/-- The literal positive inclusion gives the prescribed original mixed comparison. -/
def originalComparison : (originalLeft P d).RelHomotopy (originalRight P d) :=
  by
    let inclusion := parameterLoopingMap
      (boundedFlatCoefficientBassPositiveConeInclusion P ((laurentUnderFunctor R).obj d))
    let J := (supportedComparison P d).postcomp inclusion
    apply J.ofLevels (originalLeft P d) (originalRight P d)
    · intro n
      apply ContinuousMap.ext
      rintro ⟨r, x⟩
      exact (supportedLeft_mapped P d n x r).symm
    · intro n
      apply ContinuousMap.ext
      rintro ⟨r, x⟩
      exact (supportedRight_mapped P d n x r).symm

end Quillen.PerfectComplexes.CoefficientBassNegativeActualMixedFiller
