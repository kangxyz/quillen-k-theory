/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeActualRightRoute
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveMixedAssembly
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeActualLeftNative
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenSurfaceBoundary

/-! Assemble the actual original composite mixed filler from the two proved carrier routes. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassCompositeActualMixedFiller
open CommonReferenceNerve CoefficientBassCompositeActualLeftRoute
open CoefficientBassCompositeMixedRoutes
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- Both actual continuous routes share whole endpoint paths and retain the two separate tips. -/
def surfaces : CutOpenCarrier.RouteSurfaces (polyRef P p q) (chart P p q) (laurentRef P p q)
    (ordinary P p q) (shifted P p q) where
  left := CoefficientBassCompositeActualLeftRoute.route P p q
  right := CoefficientBassCompositeActualRightRoute.route P p q
  start := CoefficientBassCompositeActualLeftRoute.start P p q
  finish := CoefficientBassCompositeActualLeftRoute.finish P p q
  left_start := CoefficientBassCompositeActualLeftRoute.route_start P p q
  left_finish := CoefficientBassCompositeActualLeftRoute.route_finish P p q
  right_start := CoefficientBassCompositeActualRightRoute.route_start P p q
  right_finish := CoefficientBassCompositeActualRightRoute.route_finish P p q
  left_zero := CoefficientBassCompositeActualLeftRoute.route_bottom P p q
  left_one := CoefficientBassCompositeActualLeftRoute.route_top P p q
  right_zero := CoefficientBassCompositeActualRightRoute.route_bottom P p q
  right_one := CoefficientBassCompositeActualRightRoute.route_top P p q

/-- The complete six-face boundary is derived from the actual routes and their proved edges. -/
def boundary := (surfaces P p q).boundary

/-- Whole native route recovery uses the actual two comparison surfaces at every degree. -/
theorem recovers : (boundary P p q).RecoversRoutes (supportedLeft P p q) (supportedRight P p q) :=
  (surfaces P p q).recoversRoutes (supportedLeft P p q) (supportedRight P p q)
    (CoefficientBassCompositeActualLeftNative.route_native P p q)
    (CoefficientBassCompositeActualRightRoute.route_native P p q)

/-- The exact original supported composite mixed comparison, with no boundary premise. -/
def supportedComparison : (supportedLeft P p q).RelHomotopy (supportedRight P p q) :=
  (boundary P p q).relativeComparison (supportedLeft P p q) (supportedRight P p q) (recovers P p q)

/-- The literal positive inclusion gives the prescribed original mixed comparison. -/
def originalComparison : (originalLeft P p q).RelHomotopy (originalRight P p q) :=
  by
    let inclusion := parameterLoopingMap
      (boundedFlatCoefficientBassPositiveConeInclusion P c)
    let J := (supportedComparison P p q).postcomp inclusion
    apply J.ofLevels (originalLeft P p q) (originalRight P p q)
    · intro n
      apply ContinuousMap.ext
      rintro ⟨r, x⟩
      exact (supportedLeft_mapped P p q n x r).symm
    · intro n
      apply ContinuousMap.ext
      rintro ⟨r, x⟩
      exact (supportedRight_mapped P p q n x r).symm

end Quillen.PerfectComplexes.CoefficientBassCompositeActualMixedFiller
