/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveSupport

/-! Named consumers of the original positive support, its literal seed and the entire fixed-C1
moving-null reassociation. Comparison, cone, output-loop and structure times stay independent. -/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen Quillen.LoopPrespectrum Quillen.PerfectComplexes CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.CoefficientBassPositiveSupport
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The positive factor still lands in the exact original two-chart seed at every loop time. -/
theorem original_seed_all_times (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P a).map n
      (Path.toContinuousMap ((boundedFlatCoefficientBassPositiveConeSeed P a).map n x) s) =
      Path.toContinuousMap ((boundedFlatCoefficientBassTransition P a).map n x) s :=
  congrArg (fun k ↦ Path.toContinuousMap (k.map n x) s)
    (boundedFlatCoefficientBassPositiveConeSeed_factor P a)

/-- The complete original null is retained pointwise, including the midpoint of its two halves. -/
theorem original_null_all_times (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P a).map n
      ((boundedFlatCoefficientBassPositiveConeNull P a).level n (s, x)) =
      (boundedFlatCoefficientBassLaurentNullHomotopy P a).level n (s, x) :=
  DFunLike.congr_fun (boundedFlatCoefficientBassPositiveConeNull_factor P a n) (s, x)

/-- At level zero the complete cylinder has the same original cone time, without a pause. -/
theorem full_cylinder_level_zero (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space 0) :
    (boundedFlatCoefficientBassPositiveConeInclusion P a).map 0
      (ReducedMappingCone.cylinder _ _
        ((boundedFlatPerfectPrespectrumMap (laurentPlus P a)).map 0) (s, x)) =
      ReducedMappingCone.cylinder _ _ ((boundedFlatCoefficientBassSquareComparison P a).map 0)
        (s, (HomotopyPushout.inl
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map 0 x) :=
  boundedFlatCoefficientBassPositiveConeInclusion_cylinder P a 0 s x

/-- The auxiliary seed is based on the entire original connective level-zero space. -/
theorem seed_based_level_zero (s : unitInterval) :
    Path.toContinuousMap ((boundedFlatCoefficientBassPositiveConeSeed P a).map 0
      ((originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point 0)) s =
      (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a))).point 0 :=
  congrArg (fun p ↦ Path.toContinuousMap p s)
    ((boundedFlatCoefficientBassPositiveConeSeed P a).map_point 0)

/-- The original null's time is independent of the source prespectrum structure time. -/
theorem null_independent_structure (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeNull P a).level (n + 1)
      (s, (originalPrespectrum
        (boundedFlatPerfectWaldhausen (space (op P, a)))).structureMap n x t) =
      (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a))).structureMap n
        ((boundedFlatCoefficientBassPositiveConeNull P a).level n (s, x)) t :=
  (boundedFlatCoefficientBassPositiveConeNull P a).comm n s x t

/-- Seed output-loop time remains independent of the prespectrum structure time. -/
theorem seed_independent_structure (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    Path.toContinuousMap ((boundedFlatCoefficientBassPositiveConeSeed P a).map (n + 1)
      ((originalPrespectrum
        (boundedFlatPerfectWaldhausen (space (op P, a)))).structureMap n x t)) s =
      (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a))).structureMap n
        (Path.toContinuousMap ((boundedFlatCoefficientBassPositiveConeSeed P a).map n x) s) t :=
  congrArg (fun p ↦ Path.toContinuousMap (p t) s)
    ((boundedFlatCoefficientBassPositiveConeSeed P a).comm n x)

/-- The fixed positive second chart only evaluates the literal positive support of the seed. -/
theorem fixed_second_positive_seed (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    Path.toContinuousMap ((boundedFlatCoefficientBassSecondPlusHomotopy P a).level n
      (r, (boundedFlatCoefficientBassTransition P a).map n x)) s =
      (boundedFlatCoefficientBassPositiveConeComposition P
        ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a)).level n
          (r, Path.toContinuousMap ((boundedFlatCoefficientBassPositiveConeSeed P a).map n x) s) :=
  boundedFlatCoefficientBassPositiveConeComposition_seed P
    ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a) n r s x

variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The full cylinder formula retains both composition and cylinder coordinates. -/
theorem fixed_composition_full_cylinder (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeComposition P u v).level n
      (r, ReducedMappingCone.cylinder _ _
        ((boundedFlatPerfectPrespectrumMap (laurentPlus P a)).map n) (s, x)) =
      (boundedFlatCoefficientBassPositiveSupportSquare P u v).level n
        (r, (s, (HomotopyPushout.inl
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) :=
  boundedFlatCoefficientBassPositiveConeComposition_cylinder P u v n r s x

/-- The actual collapse exposes the full original relative pasting, not merely its first square. -/
theorem fixed_composition_relative_boundary (n : ℕ) (z : unitInterval × unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeComposition P u v).level n
      ((ThreeSideSquare.collapse z).1, ReducedMappingCone.cylinder _ _
        ((boundedFlatPerfectPrespectrumMap (laurentPlus P a)).map n)
        ((ThreeSideSquare.collapse z).2, x)) =
      (boundedFlatCoefficientBassPositiveSupportBoundary P u v).level n
        (z.1, (z.2, (HomotopyPushout.inl
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) :=
  boundedFlatCoefficientBassPositiveConeComposition_cylinder_collapse P u v n z x

/-- The full relative pasting fixes the original source endpoint through every comparison time. -/
theorem relative_boundary_source_fixed (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassPositiveSupportBoundary P u v).level n
      (r, (0, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) =
    (boundedFlatCoefficientBassPositiveSupportBoundary P u v).level n
      (0, (0, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) :=
  (((boundedFlatCoefficientBassPositiveSupportBoundary P u v).level n).eq_fst r
    (Or.inl rfl)).trans
    (((boundedFlatCoefficientBassPositiveSupportBoundary P u v).level n).apply_zero _).symm

/-- The full relative pasting also fixes the original terminal endpoint in degree zero. -/
theorem relative_boundary_target_fixed_zero (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space 0) :
    (boundedFlatCoefficientBassPositiveSupportBoundary P u v).level 0
      (r, (1, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map 0 x)) =
    (boundedFlatCoefficientBassPositiveSupportBoundary P u v).level 0
      (0, (1, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map 0 x)) :=
  (((boundedFlatCoefficientBassPositiveSupportBoundary P u v).level 0).eq_fst r
    (Or.inr (Or.inl rfl))).trans
    (((boundedFlatCoefficientBassPositiveSupportBoundary P u v).level 0).apply_zero _).symm

/-- Relative comparison, path and structure coordinates remain three independent parameters
on the original positive chart's image in the whole span. -/
theorem relative_boundary_independent_structure (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassPositiveSupportBoundary P u v).level (n + 1)
      (r, (s, (HomotopyPushout.prespectrum
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).structureMap n
          ((HomotopyPushout.inl
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x) t)) =
      (mappingCone (boundedFlatCoefficientBassSquareComparison P c)).structureMap n
        ((boundedFlatCoefficientBassPositiveSupportBoundary P u v).level n
          (r, (s, (HomotopyPushout.inl
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x))) t :=
  (boundedFlatCoefficientBassPositiveSupportBoundary P u v).comm n r s _ t

end QuillenTest.CoefficientBassPositiveSupport
