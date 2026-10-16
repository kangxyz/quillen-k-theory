/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.ConeSquareMapSupport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveSupport

/-!
# Independence of the positive support from the whole interior cube

Two actual interior cubes with the same required original chart faces induce exactly the same
composition homotopy on the genuine positive subcone. This follows pointwise through the entire
moving-null construction, and then through the actual cone quotient and original seed factor.
It compares supplied cubes with their full prescribed boundary types; it supplies no missing
mixed C0/J0/C1 compatibility and does not construct a second tower transition.
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
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (Q Q' : BoundedFlatCoefficientBassCompositionInteriorCube P u v)

/-- Every positive cylinder point is independent of the chosen interior, since both actual
cubes retain the same original positive chart square, including its terminal pause. -/
theorem boundedFlatCoefficientBassConeComposition_positive_cylinder_independent
    (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v Q).level n
      (r, ReducedMappingCone.cylinder _ _ ((boundedFlatCoefficientBassSquareComparison P a).map n)
        (s, (HomotopyPushout.inl
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) =
    (boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v Q').level n
      (r, ReducedMappingCone.cylinder _ _ ((boundedFlatCoefficientBassSquareComparison P a).map n)
        (s, (HomotopyPushout.inl
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) := by
  exact coneSquareCompositionMovingNullSquare_apply_congr
    (boundedFlatCoefficientBassSquareComparison P a)
    (boundedFlatCoefficientBassSquareComparison P b)
    (boundedFlatCoefficientBassSquareComparison P c)
    (boundedFlatCoefficientPolynomialSpanMap P u)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedFlatCoefficientPolynomialSpanMap P v)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map v)))
    (boundedFlatCoefficientBassComparisonHomotopy P u)
    (boundedFlatCoefficientBassComparisonHomotopy P v)
    (boundedFlatCoefficientBassComparisonHomotopy P (u ≫ v))
    (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v)
    (boundedFlatCoefficientLaurentCompositionHomotopy P u v)
    (boundedFlatCoefficientBassComparisonSquareOfInteriorCube P u v Q)
    (boundedFlatCoefficientBassComparisonSquareOfInteriorCube P u v Q') n _
    (fun r' s' ↦
      (boundedFlatCoefficientBassComparisonSquareOfInteriorCube_inl P u v Q n r' s' x).trans
        (boundedFlatCoefficientBassComparisonSquareOfInteriorCube_inl P u v Q' n r' s' x).symm)
    r s

/-- Cone extensionality turns the two genuine restriction formulas into equality on the entire
positive subcone. The original Laurent face is retained alongside every positive cylinder. -/
theorem boundedFlatCoefficientBassPositiveConeComposition_independent :
    Homotopy.precomp (boundedFlatCoefficientBassPositiveConeInclusion P a)
      (boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v Q) =
    Homotopy.precomp (boundedFlatCoefficientBassPositiveConeInclusion P a)
      (boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v Q') := by
  have h (r : unitInterval) :
      boundedFlatCoefficientBassPositiveConeInclusion P a ≫
        (boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v Q).at r =
      boundedFlatCoefficientBassPositiveConeInclusion P a ≫
        (boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v Q').at r := by
    apply mappingCone_hom_ext
    · apply Hom.ext
      funext n
      ext x
      rfl
    · intro n s x
      exact boundedFlatCoefficientBassConeComposition_positive_cylinder_independent
        P u v Q Q' n r s x
  apply Quillen.LoopPrespectrum.Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨r, x⟩
  exact congrArg (fun k ↦ k.map n x) (h r)

/-- The existing original seed therefore sees exactly the same parameter-looped composition,
with comparison and output-loop times independent. No substitute seed is used. -/
theorem boundedFlatCoefficientBassStepComposition_seed_independent :
    Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
      (boundedFlatCoefficientBassStepCompositionOfInteriorCube P u v Q) =
    Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
      (boundedFlatCoefficientBassStepCompositionOfInteriorCube P u v Q') := by
  have h := boundedFlatCoefficientBassPositiveConeComposition_independent P u v Q Q'
  apply Quillen.LoopPrespectrum.Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨r, x⟩
  apply Path.ext
  funext s
  have hs := congrArg (fun k ↦ Path.toContinuousMap (k.map n x) s)
    (boundedFlatCoefficientBassPositiveConeSeed_factor P a)
  change (boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v Q).level n
      (r, Path.toContinuousMap ((boundedFlatCoefficientBassTransition P a).map n x) s) =
    (boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v Q').level n
      (r, Path.toContinuousMap ((boundedFlatCoefficientBassTransition P a).map n x) s)
  exact (congrArg (fun y ↦
      (boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v Q).level n (r, y))
        hs).symm.trans
    ((congrArg (fun H ↦ H.level n
      (r, Path.toContinuousMap
        ((boundedFlatCoefficientBassPositiveConeSeed P a).map n x) s)) h).trans
      (congrArg (fun y ↦
        (boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v Q').level n (r, y)) hs))

/-- The actual fixed whole composition has the same positive support as any other actual cube
with those required chart faces. This does not assert higher compatibility of its chosen J0. -/
theorem boundedFlatCoefficientBassPositiveConeComposition_fixed :
    boundedFlatCoefficientBassPositiveConeComposition P u v =
      Homotopy.precomp (boundedFlatCoefficientBassPositiveConeInclusion P a)
        (boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v Q) :=
  boundedFlatCoefficientBassPositiveConeComposition_independent P u v
    (BassMWhole.interiorCube P u v) Q

/-- On the original seed, the fixed second positive chart is likewise insensitive to the
interior choice while keeping the exact prescribed positive chart boundary. -/
theorem boundedFlatCoefficientBassStepComposition_seed_fixed :
    Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
      (BassMWhole.stepComposition P u v) =
    Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
      (boundedFlatCoefficientBassStepCompositionOfInteriorCube P u v Q) :=
  boundedFlatCoefficientBassStepComposition_seed_independent P u v
    (BassMWhole.interiorCube P u v) Q

end Quillen.PerfectComplexes
