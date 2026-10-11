/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatLaurentUnitSquareHomotopy

/-! Literal geometric faces and independent structure time of the actual Laurent-unit square. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.LoopPrespectrum
open Quillen.Scheme.PolynomialLaurent Quillen.PolynomialBaseChange Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.Tests.LaurentUnitCoefficientSquare
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The source face is the original old unit loop mapped by actual Laurent coefficient change. -/
theorem old_unit (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatLaurentUnitCoefficientSquare f).level n (0, (s, x)) =
      (boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f))).map n
        ((boundedFlatLaurentUnitHomotopy R).level n (s, x)) :=
  (boundedFlatLaurentUnitCoefficientSquare f).at_zero n s x

/-- The target face is the original new unit loop on the actual base coefficient image. -/
theorem new_unit (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatLaurentUnitCoefficientSquare f).level n (1, (s, x)) =
      (boundedFlatLaurentUnitHomotopy S).level n
        (s, (boundedFlatPerfectPrespectrumMap (Spec.map f)).map n x) :=
  (boundedFlatLaurentUnitCoefficientSquare f).at_one n s x

/-- The left endpoint moves through the exact original Laurent coefficient square. -/
theorem left_endpoint (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatLaurentUnitCoefficientSquare f).level n (r, (0, x)) =
      (boundedFlatLaurentCoefficientSquareHomotopy f).level n (r, x) :=
  (boundedFlatLaurentUnitCoefficientSquare f).left n r x

/-- The right endpoint moves through the same full original coefficient track. -/
theorem right_endpoint (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatLaurentUnitCoefficientSquare f).level n (r, (1, x)) =
      (boundedFlatLaurentCoefficientSquareHomotopy f).level n (r, x) :=
  (boundedFlatLaurentUnitCoefficientSquare f).right n r x

/-- Unit time, coefficient comparison time and spectrum structure time are independent. -/
theorem three_parameters (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatLaurentUnitCoefficientSquare f).level (n + 1)
      (r, (s, (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).structureMap n x t)) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (Spec (.of (LaurentPolynomial S))))).structureMap n
          ((boundedFlatLaurentUnitCoefficientSquare f).level n (r, (s, x))) t :=
  (boundedFlatLaurentUnitCoefficientSquare f).comm n r s x t

end Quillen.Tests.LaurentUnitCoefficientSquare
