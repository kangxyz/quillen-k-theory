/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassTransitionNaturality

/-! Named consumers of actual native initial-seed coefficient naturality.
They retain the forward scalar, original positive null and cone map, literal seed endpoints,
and independent comparison, output-loop and structure coordinates, including level zero. -/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.CoefficientBassTransitionNaturality
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- The forward coordinate is the actual coefficient-pulled scalar on both native fibers. -/
theorem original_forward_scalar :
    Units.map (coefficientMap P ((laurentUnderFunctor R).map u)).appTop.hom.toMonoidHom
      (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
        (laurentGlobalUnit a.right)) =
      boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj b)
        (laurentGlobalUnit b.right) :=
  boundedFlatCoefficientLaurentUnit_coefficient P u

/-- Mapping the actual source null retains its old positive leg and original cone-square map. -/
theorem mapped_original_null (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassConeMap P u).map n
      ((boundedFlatCoefficientBassLaurentNullHomotopy P a).level n (s, x)) =
      ((CoefficientBassNullTrack.oldPositive P u).trans
        ((CoefficientBassNullTrack.positiveMovement P u).trans
          (CoefficientBassNullTrack.oldCone P u))).level n (s, x) :=
  DFunLike.congr_fun (CoefficientBassNullTrack.originalOldNull_level P u n) (s, x)

/-- At the source endpoint the literal old seed is followed by the original coefficient cone map. -/
theorem original_source_endpoint (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P u).level n (0, x)) s =
      (boundedFlatCoefficientBassConeMap P u).map n
        (Path.toContinuousMap ((boundedFlatCoefficientBassTransition P a).map n x) s) := by
  rw [Homotopy.at_zero]
  rfl

/-- At the target endpoint the original base coefficient map precedes the unchanged target seed. -/
theorem original_target_endpoint (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P u).level n (1, x)) s =
      Path.toContinuousMap ((boundedFlatCoefficientBassTransition P b).map n
        ((boundedFlatPerfectPrespectrumMap (coefficientMap P u)).map n x)) s := by
  rw [Homotopy.at_one]
  rfl

/-- Comparison time and output-loop time retain the entire original relative conjugation. -/
theorem independent_loop_coordinates (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P u).level n (r, x)) s =
      (CoefficientBassTransitionTrack.conjugateComparison P u).level n (r, (s, x)) :=
  boundedFlatCoefficientBassTransitionCoefficientHomotopy_apply P u n r s x

/-- The same actual comparison includes the original level-zero space. -/
theorem original_level_zero (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P u).level 0 (r, x)) s =
      (CoefficientBassTransitionTrack.conjugateComparison P u).level 0 (r, (s, x)) :=
  boundedFlatCoefficientBassTransitionCoefficientHomotopy_apply P u 0 r s x

/-- The original structure time is independent of both comparison and output-loop coordinates. -/
theorem independent_structure_coordinate (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P u).level (n + 1)
        (r, (originalPrespectrum (boundedFlatPerfectWaldhausen
          (space (op P, a)))).structureMap n x t)) s =
      (mappingCone (boundedFlatCoefficientBassSquareComparison P b)).structureMap n
        (Path.toContinuousMap
          ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P u).level n (r, x)) s) t :=
  congrArg (fun p ↦ Path.toContinuousMap p s)
    ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P u).comm n r x t)

/-- The actual native based point is fixed throughout both independent parameters. -/
theorem original_based_point (n : ℕ) (r s : unitInterval) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P u).level n
        (r, (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point n)) s =
      (mappingCone (boundedFlatCoefficientBassSquareComparison P b)).point n :=
  congrArg (fun p ↦ Path.toContinuousMap p s)
    ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P u).at_point n r)

end QuillenTest.CoefficientBassTransitionNaturality
