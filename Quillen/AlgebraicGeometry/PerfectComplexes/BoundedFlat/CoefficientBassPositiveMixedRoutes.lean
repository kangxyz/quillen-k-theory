/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveTransitionNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveSupportCompositionFactor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSecondStep

/-!
# Exact positive mixed projection routes

The two supported routes use the chosen initial-seed naturality, unchanged C0 positive chart
and exact paused C1 support. Their complete strict-inclusion images are the prescribed original
routes. This extracts a boundary; it supplies no relative comparison between its two routes.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveMixedRoutes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The supported fixed positive C1 uses only the literal p followed by q equals l source cast. -/
def positiveComposition :
    Homotopy
      (parameterLoopingMap (boundedFlatCoefficientBassPositiveConeMap P
        ((laurentUnderCoefficient R).app a)))
      (parameterLoopingMap (boundedFlatCoefficientBassPositiveConeMap P
        ((polynomialUnderCoefficient R).app a)) ≫
        parameterLoopingMap (boundedFlatCoefficientBassPositiveConeMap P
          ((underToLaurent R).app a))) :=
  (CoefficientBassPositiveCompositionTrack.stepComposition P
    ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a)).cast
      (congrArg (fun k ↦ parameterLoopingMap (boundedFlatCoefficientBassPositiveConeMap P k))
        (polynomialUnderCoefficient_toLaurent R a)) rfl

/-- The original left route first moves the Laurent chart seed, then the polynomial seed. -/
def originalLeft :=
  ((Homotopy.precomp
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderCoefficient R).app a)))
    (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
      ((underToLaurent R).app a)).symm).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P
      ((polynomialUnderCoefficient R).app a)).symm.postcomp
        (boundedFlatCoefficientBassStepMap P ((underToLaurent R).app a)))

/-- The original right route retains the single C0 reversal, chosen Laurent J0 and fixed C1. -/
def originalRight :=
  ((boundedFlatCoefficientLaurentPlusHomotopy P a).postcomp
    (boundedFlatCoefficientBassTransition P ((laurentUnderFunctor R).obj a))).symm.trans
      ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P
        ((laurentUnderCoefficient R).app a)).symm.trans
          ((Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
            (boundedFlatCoefficientBassSecondPlusHomotopy P a)).cast
              rfl (Category.assoc _ _ _).symm))

/-- The supported left route keeps the two original reversed J0 recipes and their exact halves. -/
def supportedLeft :=
  ((Homotopy.precomp
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderCoefficient R).app a)))
    (boundedFlatCoefficientBassPositiveTransitionHomotopy P
      ((underToLaurent R).app a)).symm).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((boundedFlatCoefficientBassPositiveTransitionHomotopy P
      ((polynomialUnderCoefficient R).app a)).symm.postcomp
        (parameterLoopingMap (boundedFlatCoefficientBassPositiveConeMap P
          ((underToLaurent R).app a))))

/-- The supported right route keeps C0, the original seed/null recipe, and the paused C1 factor. -/
def supportedRight :=
  ((boundedFlatCoefficientLaurentPlusHomotopy P a).postcomp
    (boundedFlatCoefficientBassPositiveConeSeed P ((laurentUnderFunctor R).obj a))).symm.trans
      ((boundedFlatCoefficientBassPositiveTransitionHomotopy P
        ((laurentUnderCoefficient R).app a)).symm.trans
          ((Homotopy.precomp (boundedFlatCoefficientBassPositiveConeSeed P a)
            (positiveComposition P a)).cast rfl (Category.assoc _ _ _).symm))

/-- The whole supported left path has the prescribed original image, without changing its time. -/
theorem supportedLeft_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (supportedLeft P a).MappedAt
      (parameterLoopingMap
        (boundedFlatCoefficientBassPositiveConeInclusion P ((laurentUnderFunctor R).obj a)))
      n x (originalLeft P a) := by
  unfold supportedLeft originalLeft
  apply Homotopy.MappedAt.trans
  · intro r
    apply Path.ext
    funext s
    exact boundedFlatCoefficientBassPositiveTransitionHomotopy_factor P
      ((underToLaurent R).app a) n (unitInterval.symm r) s
      ((boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((polynomialUnderCoefficient R).app a))).map n x)
  · intro r
    have hJ :
        (parameterLoopingMap (boundedFlatCoefficientBassPositiveConeInclusion P
          ((polynomialUnderFunctor R).obj a))).map n
            ((boundedFlatCoefficientBassPositiveTransitionHomotopy P
              ((polynomialUnderCoefficient R).app a)).symm.level n (r, x)) =
        (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
          ((polynomialUnderCoefficient R).app a)).symm.level n (r, x) := by
      apply Path.ext
      funext s
      exact boundedFlatCoefficientBassPositiveTransitionHomotopy_factor P
        ((polynomialUnderCoefficient R).app a) n (unitInterval.symm r) s x
    exact (congrArg (fun k ↦ k.map n
      ((boundedFlatCoefficientBassPositiveTransitionHomotopy P
        ((polynomialUnderCoefficient R).app a)).symm.level n (r, x)))
      (boundedFlatCoefficientBassPositiveConeMap_loop_factor P
        ((underToLaurent R).app a)).symm).trans
          (congrArg ((boundedFlatCoefficientBassStepMap P
            ((underToLaurent R).app a)).map n) hJ)

/-- The whole supported right path has the prescribed image, including the fixed paused C1. -/
theorem supportedRight_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (supportedRight P a).MappedAt
      (parameterLoopingMap
        (boundedFlatCoefficientBassPositiveConeInclusion P ((laurentUnderFunctor R).obj a)))
      n x (originalRight P a) := by
  unfold supportedRight originalRight
  apply Homotopy.MappedAt.trans
  · apply Homotopy.MappedAt.symm
    intro r
    exact congrArg (fun k ↦ k.map n ((boundedFlatCoefficientLaurentPlusHomotopy P a).level n
      (r, x))) (boundedFlatCoefficientBassPositiveConeSeed_factor P
        ((laurentUnderFunctor R).obj a))
  · apply Homotopy.MappedAt.trans
    · intro r
      apply Path.ext
      funext s
      exact boundedFlatCoefficientBassPositiveTransitionHomotopy_factor P
        ((laurentUnderCoefficient R).app a) n (unitInterval.symm r) s x
    · intro r
      apply Path.ext
      funext s
      exact CoefficientBassPositiveCompositionTrack.stepComposition_seed P
        ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a) n r s x

/-- Every left-route value has its original image at independent path and output-loop times. -/
theorem supportedLeft_factor (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P ((laurentUnderFunctor R).obj a)).map n
      (Path.toContinuousMap ((supportedLeft P a).level n (r, x)) s) =
    Path.toContinuousMap ((originalLeft P a).level n (r, x)) s :=
  congrArg (fun p ↦ Path.toContinuousMap p s) (supportedLeft_mapped P a n x r)

/-- Every right-route value retains the original image with the same fixed pause and casts. -/
theorem supportedRight_factor (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P ((laurentUnderFunctor R).obj a)).map n
      (Path.toContinuousMap ((supportedRight P a).level n (r, x)) s) =
    Path.toContinuousMap ((originalRight P a).level n (r, x)) s :=
  congrArg (fun p ↦ Path.toContinuousMap p s) (supportedRight_mapped P a n x r)

end Quillen.PerfectComplexes.CoefficientBassPositiveMixedRoutes
