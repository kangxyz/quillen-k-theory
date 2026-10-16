/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveTransitionNaturality

/-! Full-family consumers of the exact positive support of the already chosen J0.
Comparison, output-loop and structure times remain independent, including original degree zero. -/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen Quillen.LoopPrespectrum Quillen.PerfectComplexes CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.CoefficientBassPositiveTransitionNaturality
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- The entire original level-zero J0 is retained at two independent time coordinates. -/
theorem chosen_jzero_level_zero (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    (boundedFlatCoefficientBassPositiveConeInclusion P b).map 0
      (Path.toContinuousMap
        ((boundedFlatCoefficientBassPositiveTransitionHomotopy P u).level 0 (r, x)) s) =
    Path.toContinuousMap
      ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P u).level 0 (r, x)) s :=
  boundedFlatCoefficientBassPositiveTransitionHomotopy_factor P u 0 r s x

/-- The initial comparison face uses the literal positive seed followed by the actual gamma. -/
theorem source_face_actual_seed_map (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassPositiveTransitionHomotopy P u).level n (0, x)) s =
    (boundedFlatCoefficientBassPositiveConeMap P u).map n
      (Path.toContinuousMap ((boundedFlatCoefficientBassPositiveConeSeed P a).map n x) s) :=
  congrArg (fun p ↦ Path.toContinuousMap p s)
    ((boundedFlatCoefficientBassPositiveTransitionHomotopy P u).at_zero n x)

/-- The terminal face uses the actual base coefficient map and the unchanged target seed. -/
theorem target_face_actual_seed_map (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassPositiveTransitionHomotopy P u).level n (1, x)) s =
    Path.toContinuousMap ((boundedFlatCoefficientBassPositiveConeSeed P b).map n
      ((boundedFlatPerfectPrespectrumMap (coefficientMap P u)).map n x)) s :=
  congrArg (fun p ↦ Path.toContinuousMap p s)
    ((boundedFlatCoefficientBassPositiveTransitionHomotopy P u).at_one n x)

/-- Comparison, output-loop and structure coordinates remain three independent parameters. -/
theorem three_independent_coordinates (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassPositiveTransitionHomotopy P u).level (n + 1)
        (r, (originalPrespectrum
          (boundedFlatPerfectWaldhausen (space (op P, a)))).structureMap n x t)) s =
    (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P b))).structureMap n
      (Path.toContinuousMap
        ((boundedFlatCoefficientBassPositiveTransitionHomotopy P u).level n (r, x)) s) t :=
  congrArg (fun p ↦ Path.toContinuousMap p s)
    ((boundedFlatCoefficientBassPositiveTransitionHomotopy P u).comm n r x t)

/-- Every point on the original degree-zero based line remains based throughout J0. -/
theorem based_line_level_zero (r s : unitInterval) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassPositiveTransitionHomotopy P u).level 0
        (r, (originalPrespectrum
          (boundedFlatPerfectWaldhausen (space (op P, a)))).point 0)) s =
      (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P b))).point 0 :=
  congrArg (fun p ↦ Path.toContinuousMap p s)
    ((boundedFlatCoefficientBassPositiveTransitionHomotopy P u).at_point 0 r)

/-- The full chosen relative null comparison is retained, beyond its endpoints or loop class. -/
theorem chosen_null_comparison (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P b).map n
      ((CoefficientBassPositiveNullTrack.originalNullComparison P u).level n (r, (s, x))) =
    (CoefficientBassNullTrack.originalNullComparison P u).level n (r, (s, x)) :=
  CoefficientBassPositiveNullTrack.originalNullComparison_mapped P u n x r s

/-- The original unit-pasting surface itself is retained at every coordinate. -/
theorem chosen_unit_pasting (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P b).map n
      ((CoefficientBassPositiveTransitionTrack.unitPasting P u).level n (r, (s, x))) =
    (CoefficientBassTransitionTrack.unitPasting P u).level n (r, (s, x)) :=
  CoefficientBassPositiveTransitionTrack.unitPasting_mapped P u n x r s

/-- The old null after gamma is the unchanged original mapped null, including every null time. -/
theorem chosen_old_mapped_null (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P b).map n
      ((CoefficientBassPositiveNullTrack.originalOldNull P u).level n (s, x)) =
    (CoefficientBassNullTrack.originalOldNull P u).level n (s, x) :=
  CoefficientBassPositiveTransitionTrack.originalOldNull_mapped P u n x s

end QuillenTest.CoefficientBassPositiveTransitionNaturality
