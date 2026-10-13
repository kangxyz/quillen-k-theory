/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassGeometricComparison

/-! The proved geometric Bass comparison keeps all original cylinder, loop and stable endpoints. -/
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.LoopPrespectrum Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
open Quillen.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.BassGeometricComparison

open Quillen

/-- Every component of the original target Bass loop space is attained, without a supplied track. -/
theorem target_loop_component (R : CommRingCat.{u}) (n : ℕ)
    (δ : (affineBassStep R).space (n + 1)) :
    ∃ γ : (boundedFlatAffineBassStep R).space (n + 1),
      Joined ((boundedFlatPerfectGeometricBassStepMap R).map (n + 1) γ) δ :=
  (boundedFlatPerfectGeometricBassStepMap_positiveLevel_isWeakHomotopyEquivalence R
    n).component_surjective δ

/-- The comparison is bijective on the original signed stable group, including negative degrees. -/
theorem original_signed_stable_bijective (R : CommRingCat.{u}) (q : ℤ) :
    Function.Bijective
      ((stableHomotopyFunctor q).map (boundedFlatPerfectGeometricBassStepMap R)) := by
  have := boundedFlatPerfectGeometricBassStepMap_isStableEquivalence R q
  exact ConcreteCategory.bijective_of_isIso _

/-- Every original cone-loop coordinate is mapped by the proved geometric cone comparison. -/
theorem original_cone_loop_value (R : CommRingCat.{u}) (n : ℕ)
    (γ : Path ((mappingCone (boundedFlatBassSquareComparison R)).point n)
      ((mappingCone (boundedFlatBassSquareComparison R)).point n)) (t : unitInterval) :
    Path.toContinuousMap ((boundedFlatPerfectGeometricBassStepMap R).map n γ) t =
      (boundedFlatPerfectGeometricBassConeMap R).map n (γ t) := rfl

/-- The original inclusion cylinder recovers the entire geometric relative-pasting family. -/
theorem original_cylinder_parameters (R : CommRingCat.{u}) (n : ℕ)
    (z : unitInterval × unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatPerfectBassComparisonHomotopy R).level n
      ((Quillen.ThreeSideSquare.collapse z).1,
        HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) n
          ((Quillen.ThreeSideSquare.collapse z).2, x)) =
      (boundedFlatPerfectBassInclusionDescPasting R).level n (z.1, (z.2, x)) :=
  boundedFlatPerfectBassComparisonHomotopy_collapse R n z x

end QuillenTest.BassGeometricComparison
