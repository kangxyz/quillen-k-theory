/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNativeCube

/-! Original whole comparison, cone, and parameter-looping composition from the constructed Q. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWhole
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The entire original comparison square consumes the actual constructed six-faced cube. -/
def comparisonSquare : BoundedFlatCoefficientBassComparisonCompositionSquare P u v :=
  boundedFlatCoefficientBassComparisonSquareOfInteriorCube P u v (interiorCube P u v)

/-- Whole composition of the original cone maps, with no supplied cube or compatibility premise. -/
def coneComposition :
    Homotopy (boundedFlatCoefficientBassConeMap P (u ≫ v))
      (boundedFlatCoefficientBassConeMap P u ≫ boundedFlatCoefficientBassConeMap P v) :=
  boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v (interiorCube P u v)

/-- Whole composition of the original parameter-looped Bass step maps, on all native levels. -/
def stepComposition :
    Homotopy (boundedFlatCoefficientBassStepMap P (u ≫ v))
      (boundedFlatCoefficientBassStepMap P u ≫ boundedFlatCoefficientBassStepMap P v) :=
  boundedFlatCoefficientBassStepCompositionOfInteriorCube P u v (interiorCube P u v)

/-- The whole positive original chart square survives the actual pushout descent. -/
theorem comparison_inl (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (comparisonSquare P u v).level n
      (r, (s, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) =
      (boundedFlatCoefficientBassCompositionPlusChart P u v).level n (r, (s, x)) :=
  boundedFlatCoefficientBassComparisonSquareOfInteriorCube_inl P u v (interiorCube P u v) n r s x

/-- The distinct whole inverse chart retains its original inverse-coordinate square. -/
theorem comparison_inr (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (comparisonSquare P u v).level n
      (r, (s, (HomotopyPushout.inr
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) =
      (boundedFlatCoefficientBassCompositionMinusChart P u v).level n (r, (s, x)) :=
  boundedFlatCoefficientBassComparisonSquareOfInteriorCube_inr P u v (interiorCube P u v) n r s x

/-- Every overlap point retains the three independently varying original cube coordinates. -/
theorem comparison_cylinder (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (comparisonSquare P u v).level n
      (r, (s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x))) =
      (interiorCube P u v).level n (r, (s, (t, x))) :=
  boundedFlatCoefficientBassComparisonSquareOfInteriorCube_cylinder
    P u v (interiorCube P u v) n r s t x

/-- The original Laurent composition track survives both whole quotient descents unchanged. -/
theorem cone_inclusion (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    (coneComposition P u v).level n
      (r, (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n x) =
      (boundedFlatCoefficientBassConeCompositionInclusionHomotopy P u v).level n (r, x) :=
  boundedFlatCoefficientBassConeCompositionOfInteriorCube_inclusion
    P u v (interiorCube P u v) n r x

end Quillen.PerfectComplexes.BassMWhole
