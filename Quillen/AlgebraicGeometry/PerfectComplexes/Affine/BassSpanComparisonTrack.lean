/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassBoundary
public import Quillen.Topology.Prespectrum.HomotopySquareOfPasting
public import Quillen.Topology.Prespectrum.PushoutMovingHomotopy

/-! # Actual coefficient naturality of the original bounded-flat Bass comparison

The proved geometric boundary filler descends to the original double-cylinder comparison maps.
Both original coefficient composites and the entire cylinder track are retained.
-/
@[expose] public section

open Quillen.PolynomialBaseChange
open Quillen.Waldhausen.IteratedS


open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent
  Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The target track is the whole original polynomial-span cylinder followed by Bass comparison. -/
theorem boundedFlatBassCoefficientTargetDescTrack_level (n : ℕ) :
    (boundedFlatBassCoefficientTargetDescTrack f).level n =
      ((HomotopyPushout.mapSquareHomotopy
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection S))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection S))
        (boundedFlatPerfectPrespectrumMap (Spec.map f))
        (boundedFlatPerfectPrespectrumMap (Spec.map (polynomialMap f)))
        (boundedFlatPerfectPrespectrumMap (Spec.map (polynomialMap f)))
        (boundedFlatPolynomialSquareHomotopy f) (boundedFlatPolynomialSquareHomotopy f)).postcomp
          (boundedFlatBassSquareComparison S)).level n := by
  simp only [boundedFlatBassCoefficientTargetDescTrack, Homotopy.cast_level,
    boundedFlatBassCoefficientTargetTrack, HomotopyPushout.mapSquareHomotopy,
    Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr <;> rfl

/-- The source descent equals the literal original Bass comparison followed by Laurent change. -/
theorem boundedFlatBassCoefficientSourceDesc_eq :
    HomotopyPushout.desc
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (laurentPlus R) ≫
        boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f)))
      (boundedFlatPerfectPrespectrumMap (laurentMinus R) ≫
        boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f)))
      (boundedFlatBassCoefficientSourceDescTrack f) =
    boundedFlatBassSquareComparison R ≫
      boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f)) := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    rfl

/-- The target descent equals the original polynomial-span map followed by Bass comparison. -/
theorem boundedFlatBassCoefficientTargetDesc_eq :
    HomotopyPushout.desc
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (Spec.map (polynomialMap f)) ≫
        boundedFlatPerfectPrespectrumMap (laurentPlus S))
      (boundedFlatPerfectPrespectrumMap (Spec.map (polynomialMap f)) ≫
        boundedFlatPerfectPrespectrumMap (laurentMinus S))
      (boundedFlatBassCoefficientTargetDescTrack f) =
    boundedFlatPolynomialSpanMap f ≫ boundedFlatBassSquareComparison S := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    exact DFunLike.congr_fun (boundedFlatBassCoefficientTargetDescTrack_level f n) (s, x)

/-- The actual geometric moving square descends to the two unchanged coefficient composites. -/
def boundedFlatBassComparisonCoefficientHomotopy :
    Homotopy (boundedFlatBassSquareComparison R ≫
      boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f)))
      (boundedFlatPolynomialSpanMap f ≫ boundedFlatBassSquareComparison S) :=
  (HomotopyPushout.descSquareHomotopy
    (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPlusSquareHomotopy f) (boundedFlatMinusSquareHomotopy f)
    (boundedFlatBassCoefficientDescPasting f).toSquare).cast
      (boundedFlatBassCoefficientSourceDesc_eq f) (boundedFlatBassCoefficientTargetDesc_eq f)

/-- The left polynomial endpoint moves through its unchanged positive Laurent square. -/
theorem boundedFlatBassComparisonCoefficientHomotopy_inl (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (Spec (.of (Polynomial R))))).space n) :
    (boundedFlatBassComparisonCoefficientHomotopy f).level n
      (r, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))).map n x) =
      (boundedFlatPlusSquareHomotopy f).level n (r, x) := rfl

/-- The right polynomial endpoint moves through its distinct negative Laurent square. -/
theorem boundedFlatBassComparisonCoefficientHomotopy_inr (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (Spec (.of (Polynomial R))))).space n) :
    (boundedFlatBassComparisonCoefficientHomotopy f).level n
      (r, (HomotopyPushout.inr
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))).map n x) =
      (boundedFlatMinusSquareHomotopy f).level n (r, x) := rfl

/-- The whole actual cylinder retains the square constructed from the proved geometric pasting. -/
theorem boundedFlatBassComparisonCoefficientHomotopy_cylinder (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatBassComparisonCoefficientHomotopy f).level n
      (r, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) n (s, x)) =
      (boundedFlatBassCoefficientDescPasting f).toSquare.level n (r, (s, x)) := rfl

/-- The original relative comparison is recovered on every collapsed parameter-square point. -/
theorem boundedFlatBassComparisonCoefficientHomotopy_collapse (n : ℕ)
    (z : unitInterval × unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatBassComparisonCoefficientHomotopy f).level n
      ((Quillen.ThreeSideSquare.collapse z).1, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) n
          ((Quillen.ThreeSideSquare.collapse z).2, x)) =
      (boundedFlatBassCoefficientDescPasting f).level n (z.1, (z.2, x)) :=
  (boundedFlatBassCoefficientDescPasting f).toSquare_collapse n z x

end Quillen.PerfectComplexes
