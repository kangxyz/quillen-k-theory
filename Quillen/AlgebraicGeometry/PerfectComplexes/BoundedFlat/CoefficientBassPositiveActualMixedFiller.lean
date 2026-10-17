/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveActualLeftRouteNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveMixedAssembly
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenSurfaceBoundary

/-! Assemble the actual original positive mixed filler from the two proved carrier routes. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveActualMixedFiller
open CommonReferenceNerve CoefficientBassPositiveJ0ConeBoundaries
open CoefficientBassPositiveMixedRoutes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- Both actual continuous routes share whole endpoint paths and retain the two separate tips. -/
def surfaces : CutOpenCarrier.RouteSurfaces (polyRef P d) (chart P d) (laurentRef P d)
    (ordinary P d) (shifted P d) where
  left := CoefficientBassPositiveActualLeftRoute.route P d
  right := CoefficientBassPositiveActualRightRoute.route P d
  start := CoefficientBassPositiveActualRightRoute.start P d
  finish := CoefficientBassPositiveActualRightRoute.finish P d
  left_start := CoefficientBassPositiveActualLeftRoute.route_start P d
  left_finish := CoefficientBassPositiveActualLeftRoute.route_finish P d
  right_start := CoefficientBassPositiveActualRightRoute.route_start P d
  right_finish := CoefficientBassPositiveActualRightRoute.route_finish P d
  left_zero := CoefficientBassPositiveActualLeftRoute.route_bottom P d
  left_one := CoefficientBassPositiveActualLeftRoute.route_top P d
  right_zero := CoefficientBassPositiveActualRightRoute.route_bottom P d
  right_one := CoefficientBassPositiveActualRightRoute.route_top P d

/-- The complete six-face boundary is derived from the actual routes and their proved edges. -/
def boundary : CoefficientBassPositiveMixedAssembly.Boundary P d := (surfaces P d).boundary

/-- Whole native route recovery uses the actual two comparison surfaces at every degree. -/
theorem recovers : CoefficientBassPositiveMixedAssembly.RecoversSupportedRoutes P d
    (boundary P d) :=
  (surfaces P d).recoversRoutes (supportedLeft P d) (supportedRight P d)
    (CoefficientBassPositiveActualLeftRoute.route_native P d)
    (CoefficientBassPositiveActualRightRoute.route_native P d)

/-- The exact original supported positive mixed comparison, with no boundary premise. -/
def supportedComparison : (supportedLeft P d).RelHomotopy (supportedRight P d) :=
  CoefficientBassPositiveMixedAssembly.supportedComparison P d (boundary P d) (recovers P d)

/-- The literal positive inclusion gives the prescribed original mixed comparison. -/
def originalComparison : (originalLeft P d).RelHomotopy (originalRight P d) :=
  CoefficientBassPositiveMixedAssembly.originalComparison P d (boundary P d) (recovers P d)

end Quillen.PerfectComplexes.CoefficientBassPositiveActualMixedFiller
