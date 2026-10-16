/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveSupportMap

/-! Named consumers of the actual positive coefficient cone map. Both original cylinder halves,
the full level-zero cone, and the independent output-loop and structure times are retained. -/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen Quillen.LoopPrespectrum Quillen.PerfectComplexes CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.CoefficientBassPositiveSupportMap
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- The whole cone, rather than just its Laurent face, has the literal support factorization. -/
theorem whole_positive_cone (n : ℕ)
    (x : (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a))).space n) :
    (boundedFlatCoefficientBassConeMap P u).map n
      ((boundedFlatCoefficientBassPositiveConeInclusion P a).map n x) =
    (boundedFlatCoefficientBassPositiveConeInclusion P b).map n
      ((boundedFlatCoefficientBassPositiveConeMap P u).map n x) :=
  congrArg (fun k ↦ k.map n x) (boundedFlatCoefficientBassPositiveConeMap_factor P u)

/-- The full original level-zero cylinder sees the entire comparison/null track. -/
theorem full_cylinder_level_zero (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space 0) :
    (boundedFlatCoefficientBassPositiveConeMap P u).map 0
      (ReducedMappingCone.cylinder _ _
        ((boundedFlatPerfectPrespectrumMap (laurentPlus P a)).map 0) (s, x)) =
      (boundedFlatCoefficientBassPositiveConeMapNull P u).level 0 (s, x) :=
  boundedFlatCoefficientBassPositiveConeMap_cylinder P u 0 s x

/-- The first half is the original positive chart comparison at its unchanged internal time. -/
theorem first_half_original_chart (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeMap P u).map n
      (ReducedMappingCone.cylinder _ _
        ((boundedFlatPerfectPrespectrumMap (laurentPlus P a)).map n)
        (⟨(s : ℝ) / 2, by constructor <;> linarith [s.2.1, s.2.2]⟩, x)) =
      (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b))).map n
        ((boundedFlatCoefficientPlusSquareHomotopy P u).level n (s, x)) :=
  mappingConeSquareMap_first_half _ _ _ _ _ n s x

/-- The second half is the actual target cone cylinder on the polynomial coefficient image. -/
theorem second_half_original_cylinder (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeMap P u).map n
      (ReducedMappingCone.cylinder _ _
        ((boundedFlatPerfectPrespectrumMap (laurentPlus P a)).map n)
        (⟨((s : ℝ) + 1) / 2, by constructor <;> linarith [s.2.1, s.2.2]⟩, x)) =
      ReducedMappingCone.cylinder _ _
        ((boundedFlatPerfectPrespectrumMap (laurentPlus P b)).map n)
        (s, (boundedFlatPerfectPrespectrumMap
          (coefficientMap P ((polynomialUnderFunctor R).map u))).map n x) :=
  mappingConeSquareMap_second_half _ _ _ _ _ n s x

/-- Parameter looping preserves the original support factorization at every loop coordinate. -/
theorem loop_factor_all_times (n : ℕ) (s : unitInterval)
    (x : (parameterLooping
      (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a)))).space n) :
    Path.toContinuousMap ((boundedFlatCoefficientBassStepMap P u).map n
      ((parameterLoopingMap (boundedFlatCoefficientBassPositiveConeInclusion P a)).map n x)) s =
    (boundedFlatCoefficientBassPositiveConeInclusion P b).map n
      (Path.toContinuousMap
        ((parameterLoopingMap (boundedFlatCoefficientBassPositiveConeMap P u)).map n x) s) :=
  congrArg (fun k ↦ Path.toContinuousMap (k.map n x) s)
    (boundedFlatCoefficientBassPositiveConeMap_loop_factor P u)

/-- The actual coefficient cone map respects the original structure coordinate. -/
theorem cone_map_structure (n : ℕ) (t : unitInterval)
    (x : (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a))).space n) :
    (boundedFlatCoefficientBassPositiveConeMap P u).map (n + 1)
      ((mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a))).structureMap n x t) =
    (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P b))).structureMap n
      ((boundedFlatCoefficientBassPositiveConeMap P u).map n x) t :=
  congrArg (fun p ↦ p t) ((boundedFlatCoefficientBassPositiveConeMap P u).comm n x)

/-- The comparison/null time and the original structure coordinate remain independent. -/
theorem null_independent_structure (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeMapNull P u).level (n + 1)
      (s, (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (polynomialUnderFunctor R).obj a)))).structureMap n x t) =
    (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P b))).structureMap n
      ((boundedFlatCoefficientBassPositiveConeMapNull P u).level n (s, x)) t :=
  (boundedFlatCoefficientBassPositiveConeMapNull P u).comm n s x t

/-- The full level-zero map is based on the original positive cone. -/
theorem cone_map_based_zero :
    (boundedFlatCoefficientBassPositiveConeMap P u).map 0
      ((mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a))).point 0) =
    (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P b))).point 0 :=
  (boundedFlatCoefficientBassPositiveConeMap P u).map_point 0

end QuillenTest.CoefficientBassPositiveSupportMap
