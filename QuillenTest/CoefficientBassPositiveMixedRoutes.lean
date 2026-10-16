/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveMixedRoutes

/-! Clients of the exact two positive mixed routes. The whole path/loop families, original
left/right time subdivisions, common literal endpoints and structure compatibility remain. -/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen Quillen.LoopPrespectrum Quillen.PerfectComplexes CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes.CoefficientBassPositiveMixedRoutes
universe u
namespace QuillenTest.CoefficientBassPositiveMixedRoutes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- Every level-zero left-route value retains both independent original times. -/
theorem left_level_zero (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    (boundedFlatCoefficientBassPositiveConeInclusion P ((laurentUnderFunctor R).obj a)).map 0
      (Path.toContinuousMap ((supportedLeft P a).level 0 (r, x)) s) =
    Path.toContinuousMap ((originalLeft P a).level 0 (r, x)) s :=
  supportedLeft_factor P a 0 r s x

/-- Every level-zero right-route value retains the original fixed paused composition. -/
theorem right_level_zero (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    (boundedFlatCoefficientBassPositiveConeInclusion P ((laurentUnderFunctor R).obj a)).map 0
      (Path.toContinuousMap ((supportedRight P a).level 0 (r, x)) s) =
    Path.toContinuousMap ((originalRight P a).level 0 (r, x)) s :=
  supportedRight_factor P a 0 r s x

/-- The entire first left half is the chosen Laurent J0 reversal at its original doubled time. -/
theorem left_first_half (n : ℕ) (r : unitInterval) (hr : (r : ℝ) ≤ 1 / 2)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (supportedLeft P a).level n (r, x) =
    (boundedFlatCoefficientBassPositiveTransitionHomotopy P
      ((underToLaurent R).app a)).symm.level n
        (⟨2 * r, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨r.2.1, hr⟩⟩,
          (boundedFlatPerfectPrespectrumMap
            (coefficientMap P ((polynomialUnderCoefficient R).app a))).map n x) := by
  change (((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)) = _
  rw [ContinuousMap.HomotopyRel.trans_apply, dite_eq_left hr]
  rfl

/-- The entire first right half is the single original C0 reversal followed by the old seed. -/
theorem right_first_half (n : ℕ) (r : unitInterval) (hr : (r : ℝ) ≤ 1 / 2)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (supportedRight P a).level n (r, x) =
    (boundedFlatCoefficientBassPositiveConeSeed P ((laurentUnderFunctor R).obj a)).map n
      ((boundedFlatCoefficientLaurentPlusHomotopy P a).symm.level n
        (⟨2 * r, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨r.2.1, hr⟩⟩, x)) := by
  change (((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)) = _
  rw [ContinuousMap.HomotopyRel.trans_apply, dite_eq_left hr]
  rfl

/-- The two supported routes have exactly the same source value on every original point. -/
theorem common_source (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (supportedLeft P a).level n (0, x) = (supportedRight P a).level n (0, x) :=
  ((supportedLeft P a).at_zero n x).trans ((supportedRight P a).at_zero n x).symm

/-- Both supported routes end at the same literal seed followed by the two positive maps. -/
theorem common_target (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (supportedLeft P a).level n (1, x) = (supportedRight P a).level n (1, x) :=
  ((supportedLeft P a).at_one n x).trans ((supportedRight P a).at_one n x).symm

/-- Both original target routes retain the actual common original endpoint. -/
theorem original_common_target (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (originalLeft P a).level n (1, x) = (originalRight P a).level n (1, x) :=
  ((originalLeft P a).at_one n x).trans ((originalRight P a).at_one n x).symm

/-- Original route, output-loop and structure coordinates stay independent on the left. -/
theorem left_three_coordinates (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    Path.toContinuousMap ((supportedLeft P a).level (n + 1)
      (r, (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).structureMap n
        x t)) s =
    (mappingCone (boundedFlatPerfectPrespectrumMap
      (laurentPlus P ((laurentUnderFunctor R).obj a)))).structureMap n
        (Path.toContinuousMap ((supportedLeft P a).level n (r, x)) s) t :=
  congrArg (fun p ↦ Path.toContinuousMap p s) ((supportedLeft P a).comm n r x t)

/-- Original route, output-loop and structure coordinates stay independent on the right. -/
theorem right_three_coordinates (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    Path.toContinuousMap ((supportedRight P a).level (n + 1)
      (r, (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).structureMap n
        x t)) s =
    (mappingCone (boundedFlatPerfectPrespectrumMap
      (laurentPlus P ((laurentUnderFunctor R).obj a)))).structureMap n
        (Path.toContinuousMap ((supportedRight P a).level n (r, x)) s) t :=
  congrArg (fun p ↦ Path.toContinuousMap p s) ((supportedRight P a).comm n r x t)

/-- The entire based line of the left route is the original constant based loop. -/
theorem left_based_line (r : unitInterval) :
    (supportedLeft P a).level 0
      (r, (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point 0) =
    (parameterLooping (mappingCone (boundedFlatPerfectPrespectrumMap
      (laurentPlus P ((laurentUnderFunctor R).obj a))))).point 0 :=
  (supportedLeft P a).at_point 0 r

/-- The entire based line of the right route is the same original constant based loop. -/
theorem right_based_line (r : unitInterval) :
    (supportedRight P a).level 0
      (r, (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point 0) =
    (parameterLooping (mappingCone (boundedFlatPerfectPrespectrumMap
      (laurentPlus P ((laurentUnderFunctor R).obj a))))).point 0 :=
  (supportedRight P a).at_point 0 r

end QuillenTest.CoefficientBassPositiveMixedRoutes
