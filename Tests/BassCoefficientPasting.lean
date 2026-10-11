/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassBoundary
public import Quillen.Topology.Prespectrum.HomotopySquareOfPasting

/-! An actual geometric moving Bass square, constructed without a supplied coherence hypothesis. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.LoopPrespectrum
open Quillen.Scheme.PolynomialLaurent Quillen.PolynomialBaseChange Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.Tests.BassCoefficientPasting
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- Every coefficient map supplies this actual moving square by the proved geometric filler. -/
def actualMovingSquare := (boundedFlatBassCoefficientDescPasting f).toSquare

/-- The initial cylinder retains the original Bass square under Laurent coefficient change. -/
theorem original_source (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (actualMovingSquare f).level n (0, (s, x)) =
      ((boundedFlatBassSquareHomotopy R).postcomp
        (boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f)))).level n (s, x) :=
  (actualMovingSquare f).at_zero n s x

/-- The positive endpoint moves by its literal original Laurent coefficient square. -/
theorem original_plus_movement (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (actualMovingSquare f).level n (r, (0, x)) =
      (boundedFlatPlusSquareHomotopy f).level n
        (r, (boundedFlatPerfectPrespectrumMap (polynomialProjection R)).map n x) :=
  (actualMovingSquare f).left n r x

/-- The negative endpoint retains its own original inverse-coordinate square track. -/
theorem original_minus_movement (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (actualMovingSquare f).level n (r, (1, x)) =
      (boundedFlatMinusSquareHomotopy f).level n
        (r, (boundedFlatPerfectPrespectrumMap (polynomialProjection R)).map n x) :=
  (actualMovingSquare f).right n r x

/-- The final cylinder retains the original right-associated polynomial and target Bass tracks. -/
theorem original_target (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (actualMovingSquare f).level n (1, (s, x)) =
      (boundedFlatBassCoefficientTargetTrack f).level n (s, x) :=
  (actualMovingSquare f).at_one n s x

/-- All three parameters remain independent in the actual geometric square. -/
theorem independent_structure_time (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (actualMovingSquare f).level (n + 1)
      (r, (s, (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).structureMap n x t)) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (Spec (.of (LaurentPolynomial S))))).structureMap n
        ((actualMovingSquare f).level n (r, (s, x))) t :=
  (actualMovingSquare f).comm n r s x t

end Quillen.Tests.BassCoefficientPasting
