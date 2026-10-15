/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassNullSquare

/-! Original Laurent nullhomotopies, the actual coefficient endpoint track and fixed zero. -/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.BassLaurentNullCoefficientSquare

open Quillen
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The initial face is precisely the original old nullhomotopy under the actual cone map. -/
theorem original_old_null (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatBassLaurentNullCoefficientSquare f).level n (0, (s, x)) =
      (boundedFlatBassConeMap f).map n ((boundedFlatBassLaurentNullHomotopy R).level n (s, x)) :=
  (boundedFlatBassLaurentNullCoefficientSquare f).at_zero n s x

/-- The final face is precisely the original new nullhomotopy on the actual base-map image. -/
theorem original_new_null (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatBassLaurentNullCoefficientSquare f).level n (1, (s, x)) =
      (boundedFlatBassLaurentNullHomotopy S).level n
        (s, (boundedFlatPerfectPrespectrumMap (Spec.map f)).map n x) :=
  (boundedFlatBassLaurentNullCoefficientSquare f).at_one n s x

/-- The moving source endpoint follows the exact Laurent coefficient square under cone inclusion. -/
theorem original_laurent_endpoint (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatBassLaurentNullCoefficientSquare f).level n (r, (0, x)) =
      (mappingConeInclusion (boundedFlatBassSquareComparison S)).map n
        ((boundedFlatLaurentCoefficientSquareHomotopy f).level n (r, x)) :=
  (boundedFlatBassLaurentNullCoefficientSquare f).left n r x

/-- The null endpoint remains literally the target cone point throughout the comparison. -/
theorem fixed_zero_endpoint (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatBassLaurentNullCoefficientSquare f).level n (r, (1, x)) =
      (mappingCone (boundedFlatBassSquareComparison S)).point n :=
  (boundedFlatBassLaurentNullCoefficientSquare f).right n r x

/-- Comparison, original null-path and spectrum structure times remain independent. -/
theorem three_parameters (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatBassLaurentNullCoefficientSquare f).level (n + 1)
      (r, (s, (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).structureMap n x t)) =
      (mappingCone (boundedFlatBassSquareComparison S)).structureMap n
        ((boundedFlatBassLaurentNullCoefficientSquare f).level n (r, (s, x))) t :=
  (boundedFlatBassLaurentNullCoefficientSquare f).comm n r s x t

end QuillenTest.BassLaurentNullCoefficientSquare
