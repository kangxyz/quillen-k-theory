/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
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
namespace Quillen.PerfectComplexes.CoefficientBassCompositeMixedRoutes
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The supported composition retains the original fixed cone pause and looping coordinate. -/
abbrev supportedComposition := CoefficientBassPositiveCompositionTrack.stepComposition P p q

/-- The original left route first moves the Laurent chart seed, then the polynomial seed. -/
def originalLeft :=
  ((Homotopy.precomp
    (boundedFlatPerfectPrespectrumMap (coefficientMap P p))
    (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
      q).symm).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P
      p).symm.postcomp
        (boundedFlatCoefficientBassStepMap P q))

/-- The original right route retains C0 reversal, J of the literal composite, and fixed C1. -/
def originalRight :=
  ((boundedFlatCoefficientCompositionHomotopy P p q).postcomp
    (boundedFlatCoefficientBassTransition P c)).symm.trans
      ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P
        (p ≫ q)).symm.trans
          ((Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
            (BassMWhole.stepComposition P p q)).cast
              rfl (Category.assoc _ _ _).symm))

/-- The supported left route keeps the two original reversed J0 recipes and their exact halves. -/
def supportedLeft :=
  ((Homotopy.precomp
    (boundedFlatPerfectPrespectrumMap (coefficientMap P p))
    (boundedFlatCoefficientBassPositiveTransitionHomotopy P
      q).symm).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((boundedFlatCoefficientBassPositiveTransitionHomotopy P
      p).symm.postcomp
        (parameterLoopingMap (boundedFlatCoefficientBassPositiveConeMap P
          q)))

/-- The supported right route keeps C0, the original seed/null recipe, and the paused C1 factor. -/
def supportedRight :=
  ((boundedFlatCoefficientCompositionHomotopy P p q).postcomp
    (boundedFlatCoefficientBassPositiveConeSeed P c)).symm.trans
      ((boundedFlatCoefficientBassPositiveTransitionHomotopy P
        (p ≫ q)).symm.trans
          ((Homotopy.precomp (boundedFlatCoefficientBassPositiveConeSeed P a)
            (supportedComposition P p q)).cast rfl (Category.assoc _ _ _).symm))

/-- The whole supported left path has the prescribed original image, without changing its time. -/
theorem supportedLeft_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (supportedLeft P p q).MappedAt
      (parameterLoopingMap
        (boundedFlatCoefficientBassPositiveConeInclusion P c))
      n x (originalLeft P p q) := by
  unfold supportedLeft originalLeft
  apply Homotopy.MappedAt.trans
  · intro r
    apply Path.ext
    funext s
    exact boundedFlatCoefficientBassPositiveTransitionHomotopy_factor P
      q n (unitInterval.symm r) s
      ((boundedFlatPerfectPrespectrumMap
        (coefficientMap P p)).map n x)
  · intro r
    have hJ :
        (parameterLoopingMap (boundedFlatCoefficientBassPositiveConeInclusion P
          b)).map n
            ((boundedFlatCoefficientBassPositiveTransitionHomotopy P
              p).symm.level n (r, x)) =
        (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
          p).symm.level n (r, x) := by
      apply Path.ext
      funext s
      exact boundedFlatCoefficientBassPositiveTransitionHomotopy_factor P
        p n (unitInterval.symm r) s x
    exact (congrArg (fun k ↦ k.map n
      ((boundedFlatCoefficientBassPositiveTransitionHomotopy P
        p).symm.level n (r, x)))
      (boundedFlatCoefficientBassPositiveConeMap_loop_factor P
        q).symm).trans
          (congrArg ((boundedFlatCoefficientBassStepMap P
            q).map n) hJ)

/-- The whole supported right path has the prescribed image, including the fixed paused C1. -/
theorem supportedRight_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (supportedRight P p q).MappedAt
      (parameterLoopingMap
        (boundedFlatCoefficientBassPositiveConeInclusion P c))
      n x (originalRight P p q) := by
  unfold supportedRight originalRight
  apply Homotopy.MappedAt.trans
  · apply Homotopy.MappedAt.symm
    intro r
    exact congrArg (fun k ↦ k.map n ((boundedFlatCoefficientCompositionHomotopy P p q).level n
      (r, x))) (boundedFlatCoefficientBassPositiveConeSeed_factor P
        c)
  · apply Homotopy.MappedAt.trans
    · intro r
      apply Path.ext
      funext s
      exact boundedFlatCoefficientBassPositiveTransitionHomotopy_factor P
        (p ≫ q) n (unitInterval.symm r) s x
    · intro r
      apply Path.ext
      funext s
      exact CoefficientBassPositiveCompositionTrack.stepComposition_seed P
        p q n r s x

/-- Every left-route value has its original image at independent path and output-loop times. -/
theorem supportedLeft_factor (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P c).map n
      (Path.toContinuousMap ((supportedLeft P p q).level n (r, x)) s) =
    Path.toContinuousMap ((originalLeft P p q).level n (r, x)) s :=
  congrArg (fun p ↦ Path.toContinuousMap p s) (supportedLeft_mapped P p q n x r)

/-- Every right-route value retains the original image with the same fixed pause and casts. -/
theorem supportedRight_factor (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P c).map n
      (Path.toContinuousMap ((supportedRight P p q).level n (r, x)) s) =
    Path.toContinuousMap ((originalRight P p q).level n (r, x)) s :=
  congrArg (fun p ↦ Path.toContinuousMap p s) (supportedRight_mapped P p q n x r)

end Quillen.PerfectComplexes.CoefficientBassCompositeMixedRoutes
