/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveSupportCompositionFactor

/-! Full-family clients of the exact fixed paused C1 factor. They retain the whole terminal
pause, every level-zero cone point, the entire relative null boundary and independent times. -/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen Quillen.LoopPrespectrum Quillen.PerfectComplexes CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes.CoefficientBassPositiveCompositionTrack
universe u
namespace QuillenTest.CoefficientBassPositiveSupportComposition
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Every point of the terminal half is the actual constant polynomial composite. -/
theorem entire_terminal_pause (n : ℕ) (r : unitInterval) (hr : (1 : ℝ) / 2 ≤ r)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (polynomialComposition P u v).level n (r, x) =
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map v))).map n
      ((boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((polynomialUnderFunctor R).map u))).map n x) := by
  change (((boundedFlatCoefficientPolynomialCompositionHomotopy P u v).levelHomotopy n).trans
    ((Quillen.LoopPrespectrum.Homotopy.refl _).levelHomotopy n)) (r, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · rename_i h
    have ht : (⟨2 * r,
        (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨r.2.1, h⟩⟩ : unitInterval) = 1 := by
      apply Subtype.ext
      dsimp
      linarith
    change (boundedFlatCoefficientPolynomialCompositionHomotopy P u v).level n
      (⟨2 * r, _⟩, x) = _
    rw [ht]
    exact (boundedFlatCoefficientPolynomialCompositionHomotopy P u v).at_one n x
  · rfl

/-- Every original degree-zero positive-cone point has the fixed whole C1 image. -/
theorem whole_cone_level_zero (r : unitInterval)
    (x : (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a))).space 0) :
    (boundedFlatCoefficientBassPositiveConeInclusion P c).map 0
      ((coneComposition P u v).level 0 (r, x)) =
    (BassMWhole.coneComposition P u v).level 0
      (r, (boundedFlatCoefficientBassPositiveConeInclusion P a).map 0 x) :=
  coneComposition_factor P u v 0 r x

/-- The entire degree-zero cylinder retains both original composition and cone times. -/
theorem full_cylinder_level_zero (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space 0) :
    (boundedFlatCoefficientBassPositiveConeInclusion P c).map 0
      ((coneComposition P u v).level 0
        (r, ReducedMappingCone.cylinder _ _
          ((boundedFlatPerfectPrespectrumMap (laurentPlus P a)).map 0) (s, x))) =
    (boundedFlatCoefficientBassPositiveSupportSquare P u v).level 0
      (r, (s, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map 0 x)) :=
  nullSquare_factor P u v 0 r s x

/-- The original collapse displays the whole relative null tail after strict support inclusion. -/
theorem entire_relative_boundary (n : ℕ) (z : unitInterval × unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P c).map n
      ((coneComposition P u v).level n
        ((ThreeSideSquare.collapse z).1, ReducedMappingCone.cylinder _ _
          ((boundedFlatPerfectPrespectrumMap (laurentPlus P a)).map n)
          ((ThreeSideSquare.collapse z).2, x))) =
    (boundedFlatCoefficientBassPositiveSupportBoundary P u v).level n
      (z.1, (z.2, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) :=
  (coneComposition_factor P u v n (ThreeSideSquare.collapse z).1 _).trans
    (boundedFlatCoefficientBassPositiveConeComposition_cylinder_collapse P u v n z x)

/-- Composition, output-loop and structure times remain independent in the actual looped map. -/
theorem three_independent_coordinates (n : ℕ) (r s t : unitInterval)
    (x : (parameterLooping
      (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a)))).space n) :
    Path.toContinuousMap ((stepComposition P u v).level (n + 1)
      (r, (parameterLooping (mappingCone
        (boundedFlatPerfectPrespectrumMap (laurentPlus P a)))).structureMap n x t)) s =
    (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P c))).structureMap n
      (Path.toContinuousMap ((stepComposition P u v).level n (r, x)) s) t :=
  congrArg (fun p ↦ Path.toContinuousMap p s) ((stepComposition P u v).comm n r x t)

/-- The whole original level-zero based line remains based throughout composition. -/
theorem based_line_level_zero (r : unitInterval) :
    (coneComposition P u v).level 0
      (r, (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a))).point 0) =
    (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P c))).point 0 :=
  (coneComposition P u v).at_point 0 r

/-- The source face is the actual direct positive coefficient cone map. -/
theorem actual_source_map (n : ℕ)
    (x : (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a))).space n) :
    (coneComposition P u v).level n (0, x) =
      (boundedFlatCoefficientBassPositiveConeMap P (u ≫ v)).map n x :=
  (coneComposition P u v).at_zero n x

/-- The target face is the literal composite of the two actual positive cone maps. -/
theorem actual_target_map (n : ℕ)
    (x : (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a))).space n) :
    (coneComposition P u v).level n (1, x) =
      (boundedFlatCoefficientBassPositiveConeMap P v).map n
        ((boundedFlatCoefficientBassPositiveConeMap P u).map n x) :=
  (coneComposition P u v).at_one n x

/-- The fixed second positive chart on the unchanged seed is the supported paused composition. -/
theorem fixed_second_positive_seed (a : Under R) (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P ((laurentUnderFunctor R).obj a)).map n
      (Path.toContinuousMap ((stepComposition P
        ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a)).level n
        (r, (boundedFlatCoefficientBassPositiveConeSeed P a).map n x)) s) =
    Path.toContinuousMap ((boundedFlatCoefficientBassSecondPlusHomotopy P a).level n
      (r, (boundedFlatCoefficientBassTransition P a).map n x)) s :=
  stepComposition_seed P ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a) n r s x

end QuillenTest.CoefficientBassPositiveSupportComposition
