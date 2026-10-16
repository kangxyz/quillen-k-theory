/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveSupportIndependence

/-! Named consumers of positive-support independence for actual cubes with their full chart
boundaries. They retain original seeds, fixed second positive tracks and independent coordinates. -/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen Quillen.LoopPrespectrum Quillen.PerfectComplexes CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.CoefficientBassPositiveSupportIndependence
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (Q Q' : BoundedFlatCoefficientBassCompositionInteriorCube P u v)

/-- Independence holds on every point of the genuine positive cone, not just its two endpoints. -/
theorem all_positive_cone_points (n : ℕ) (r : unitInterval)
    (x : (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a))).space n) :
    (boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v Q).level n
      (r, (boundedFlatCoefficientBassPositiveConeInclusion P a).map n x) =
    (boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v Q').level n
      (r, (boundedFlatCoefficientBassPositiveConeInclusion P a).map n x) :=
  congrArg (fun H ↦ H.level n (r, x))
    (boundedFlatCoefficientBassPositiveConeComposition_independent P u v Q Q')

/-- The complete positive cone cylinder is independent in the original level-zero space. -/
theorem level_zero_positive_cylinder (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space 0) :
    (boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v Q).level 0
      (r, ReducedMappingCone.cylinder _ _ ((boundedFlatCoefficientBassSquareComparison P a).map 0)
        (s, (HomotopyPushout.inl
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map 0 x)) =
    (boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v Q').level 0
      (r, ReducedMappingCone.cylinder _ _ ((boundedFlatCoefficientBassSquareComparison P a).map 0)
        (s, (HomotopyPushout.inl
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map 0 x)) :=
  boundedFlatCoefficientBassConeComposition_positive_cylinder_independent P u v Q Q' 0 r s x

/-- The existing seed keeps its actual output-loop coordinate independent of composition time. -/
theorem original_seed_independent_times (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassStepCompositionOfInteriorCube P u v Q).level n
        (r, (boundedFlatCoefficientBassTransition P a).map n x)) s =
    Path.toContinuousMap
      ((boundedFlatCoefficientBassStepCompositionOfInteriorCube P u v Q').level n
        (r, (boundedFlatCoefficientBassTransition P a).map n x)) s :=
  congrArg (fun H ↦ Path.toContinuousMap (H.level n (r, x)) s)
    (boundedFlatCoefficientBassStepComposition_seed_independent P u v Q Q')

/-- The unchanged Laurent face still uses the actual original Laurent composition homotopy. -/
theorem laurent_face_unchanged (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v Q).level n
      (r, (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n x) =
      (boundedFlatCoefficientBassConeCompositionInclusionHomotopy P u v).level n (r, x) :=
  boundedFlatCoefficientBassConeCompositionOfInteriorCube_inclusion P u v Q n r x

/-- The based line stays fixed in the original connective degree, at all independent times. -/
theorem original_seed_based_level_zero (r s : unitInterval) :
    Path.toContinuousMap
      ((Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
        (boundedFlatCoefficientBassStepCompositionOfInteriorCube P u v Q)).level 0
          (r, (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point 0)) s =
      (mappingCone (boundedFlatCoefficientBassSquareComparison P c)).point 0 :=
  congrArg (fun p ↦ Path.toContinuousMap p s)
    ((Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
      (boundedFlatCoefficientBassStepCompositionOfInteriorCube P u v Q)).at_point 0 r)

/-- Comparison, original seed loop and structure coordinates remain three independent times. -/
theorem original_seed_independent_structure (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    Path.toContinuousMap
      ((Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
        (boundedFlatCoefficientBassStepCompositionOfInteriorCube P u v Q)).level (n + 1)
          (r, (originalPrespectrum (boundedFlatPerfectWaldhausen
            (space (op P, a)))).structureMap n x t)) s =
      (mappingCone (boundedFlatCoefficientBassSquareComparison P c)).structureMap n
        (Path.toContinuousMap
          ((Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
            (boundedFlatCoefficientBassStepCompositionOfInteriorCube P u v Q')).level n
              (r, x)) s) t :=
  (congrArg (fun H ↦ Path.toContinuousMap (H.level (n + 1)
    (r, (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, a)))).structureMap n x t)) s)
    (boundedFlatCoefficientBassStepComposition_seed_independent P u v Q Q')).trans
      (congrArg (fun p ↦ Path.toContinuousMap p s)
        ((Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
          (boundedFlatCoefficientBassStepCompositionOfInteriorCube P u v Q')).comm n r x t))

/-- In the actual second positive chart, the fixed whole cube and any cube with its exact
prescribed chart faces agree on the existing initial seed. -/
theorem fixed_second_positive_chart (a : Under R)
    (Q : BoundedFlatCoefficientBassCompositionInteriorCube P
      ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a))
    (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    Path.toContinuousMap ((boundedFlatCoefficientBassSecondPlusHomotopy P a).level n
      (r, (boundedFlatCoefficientBassTransition P a).map n x)) s =
    Path.toContinuousMap
      ((boundedFlatCoefficientBassStepCompositionOfInteriorCube P
        ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a) Q).level n
          (r, (boundedFlatCoefficientBassTransition P a).map n x)) s :=
  congrArg (fun H ↦ Path.toContinuousMap (H.level n (r, x)) s)
    (boundedFlatCoefficientBassStepComposition_seed_fixed P
      ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a) Q)

end QuillenTest.CoefficientBassPositiveSupportIndependence
