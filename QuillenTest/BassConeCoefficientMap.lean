/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassSourceLeg

/-! Actual Bass cone maps, loop coordinates and moving source-leg nullhomotopies. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent Quillen.PolynomialBaseChange
  Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.BassConeCoefficientMap

open Quillen
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The original Laurent endpoint is unchanged by the genuine coefficient cone map. -/
theorem original_inclusion :
    mappingConeInclusion (boundedFlatBassSquareComparison R) ≫ boundedFlatBassConeMap f =
      boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f)) ≫
        mappingConeInclusion (boundedFlatBassSquareComparison S) :=
  boundedFlatBassConeMap_inclusion f

/-- The parameter-correct step map evaluates the original cone map at every loop point. -/
theorem original_loop (n : ℕ) (γ : (boundedFlatAffineBassStep R).space n) (s : unitInterval) :
    Path.toContinuousMap ((boundedFlatAffineBassStepMap f).map n γ) s =
      (boundedFlatBassConeMap f).map n (Path.toContinuousMap γ s) := rfl

/-- The actual cone cylinder retains the entire proved comparison before the target null track. -/
theorem original_cylinder (n : ℕ) (s : unitInterval)
    (x : (HomotopyPushout.prespectrum
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))).space n) :
    (boundedFlatBassConeMap f).map n
      (ReducedMappingCone.cylinder _ _ ((boundedFlatBassSquareComparison R).map n) (s, x)) =
    (((boundedFlatBassComparisonCoefficientHomotopy f).postcomp
      (mappingConeInclusion (boundedFlatBassSquareComparison S))).trans
      (Homotopy.precomp (boundedFlatPolynomialSpanMap f)
        (mappingConeHomotopy (boundedFlatBassSquareComparison S)))).level n (s, x) :=
  boundedFlatBassConeMap_cylinder f n s x

/-- The moving source leg enters the original target cone cylinder at independent times. -/
theorem original_source_leg_square (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatBassSourceLegConeSquare f).level n (r, (s, x)) =
      (mappingConeHomotopy (boundedFlatBassSquareComparison S)).level n
        (s, (boundedFlatBassSourceLegCoefficientHomotopy f).level n (r, x)) :=
  boundedFlatBassSourceLegConeSquare_apply f n r s x

/-- The actual boundary comparison keeps every original collapsed square coordinate. -/
theorem original_source_leg_boundary (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatBassSourceLegConeBoundary f).level n (r, (s, x)) =
      (boundedFlatBassSourceLegConeSquare f).level n
        ((Quillen.ThreeSideSquare.collapse (r, s)).1,
          ((Quillen.ThreeSideSquare.collapse (r, s)).2, x)) := rfl

end QuillenTest.BassConeCoefficientMap
