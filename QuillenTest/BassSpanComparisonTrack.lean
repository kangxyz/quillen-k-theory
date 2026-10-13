/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassSpanComparisonTrack

/-! # Literal composite-map and full-cylinder consumers of Bass coefficient naturality -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PerfectComplexes
open Quillen.Scheme.PolynomialLaurent Quillen.PolynomialBaseChange Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.BassSpanComparisonTrack

open Quillen
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The homotopy begins at exactly the original Bass comparison followed by Laurent change. -/
theorem original_source_map :
    (boundedFlatBassComparisonCoefficientHomotopy f).at 0 =
      boundedFlatBassSquareComparison R ≫
        boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f)) := by
  apply Hom.ext
  funext n
  ext x
  exact (boundedFlatBassComparisonCoefficientHomotopy f).at_zero n x

/-- The homotopy ends at exactly the original polynomial span map followed by Bass comparison. -/
theorem original_target_map :
    (boundedFlatBassComparisonCoefficientHomotopy f).at 1 =
      boundedFlatPolynomialSpanMap f ≫ boundedFlatBassSquareComparison S := by
  apply Hom.ext
  funext n
  ext x
  exact (boundedFlatBassComparisonCoefficientHomotopy f).at_one n x

/-- Every left time slice retains the entire original positive coefficient homotopy. -/
theorem original_left_slice (r : unitInterval) :
    HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) ≫
      (boundedFlatBassComparisonCoefficientHomotopy f).at r =
        (boundedFlatPlusSquareHomotopy f).at r := by
  apply Hom.ext
  funext n
  ext x
  exact boundedFlatBassComparisonCoefficientHomotopy_inl f n r x

/-- Every right time slice retains the distinct inverse-coordinate coefficient homotopy. -/
theorem original_right_slice (r : unitInterval) :
    HomotopyPushout.inr
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) ≫
      (boundedFlatBassComparisonCoefficientHomotopy f).at r =
        (boundedFlatMinusSquareHomotopy f).at r := by
  apply Hom.ext
  funext n
  ext x
  exact boundedFlatBassComparisonCoefficientHomotopy_inr f n r x

/-- The structure coordinate remains independent of comparison and source-cylinder coordinates. -/
theorem original_three_parameters (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatBassComparisonCoefficientHomotopy f).level (n + 1)
      (r, (HomotopyPushout.prespectrum
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))).structureMap n
          (HomotopyPushout.cylinder
            (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) n (s, x)) t) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (Spec (.of (LaurentPolynomial S))))).structureMap n
        ((boundedFlatBassCoefficientDescPasting f).toSquare.level n (r, (s, x))) t :=
  (boundedFlatBassComparisonCoefficientHomotopy f).comm n r _ t

/-- The descended original cylinder recovers every point of the proved geometric relative filler. -/
theorem original_relative_filler (n : ℕ) (z : unitInterval × unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatBassComparisonCoefficientHomotopy f).level n
      ((Quillen.ThreeSideSquare.collapse z).1, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) n
          ((Quillen.ThreeSideSquare.collapse z).2, x)) =
      (boundedFlatBassCoefficientDescPasting f).level n (z.1, (z.2, x)) :=
  boundedFlatBassComparisonCoefficientHomotopy_collapse f n z x

end QuillenTest.BassSpanComparisonTrack
