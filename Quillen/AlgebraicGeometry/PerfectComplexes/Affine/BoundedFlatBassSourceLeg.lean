/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassStepMap
public import Quillen.Topology.Prespectrum.HomotopySquareInterchange
public import Quillen.Topology.Prespectrum.HomotopySquareBoundary

/-! Original polynomial source-leg movement and the actual target cone-cylinder square. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.Scheme.PolynomialLaurent Quillen.PolynomialBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The original source leg maps to the literal positive polynomial endpoint. -/
lemma boundedFlatBassSourceLeg_span :
    boundedFlatBassSourceLeg R ≫ boundedFlatPolynomialSpanMap f =
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R) ≫
        boundedFlatPerfectPrespectrumMap (Spec.map (polynomialMap f))) ≫
          HomotopyPushout.inl
            (boundedFlatPerfectPrespectrumMap (polynomialProjection S))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection S)) := by
  unfold boundedFlatBassSourceLeg
  rw [Category.assoc, inl_boundedFlatPolynomialSpanMap, Category.assoc]

/-- The actual polynomial coefficient square moves the original source leg through the target. -/
def boundedFlatBassSourceLegCoefficientHomotopy :
    Homotopy (boundedFlatBassSourceLeg R ≫ boundedFlatPolynomialSpanMap f)
      (boundedFlatPerfectPrespectrumMap (Spec.map f) ≫ boundedFlatBassSourceLeg S) :=
  ((boundedFlatPolynomialSquareHomotopy f).postcomp (HomotopyPushout.inl
    (boundedFlatPerfectPrespectrumMap (polynomialProjection S))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection S)))).cast
      (boundedFlatBassSourceLeg_span f).symm (Category.assoc _ _ _)

/-- Moving the source leg through the original cone nullhomotopy gives an actual square. -/
def boundedFlatBassSourceLegConeSquare :=
  Homotopy.Square.interchange (boundedFlatBassSourceLegCoefficientHomotopy f)
    (mappingConeHomotopy (boundedFlatBassSquareComparison S))

/-- Its whole cylinder retains the two independent original geometric parameters. -/
lemma boundedFlatBassSourceLegConeSquare_apply (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatBassSourceLegConeSquare f).level n (r, (s, x)) =
      (mappingConeHomotopy (boundedFlatBassSquareComparison S)).level n
        (s, (boundedFlatBassSourceLegCoefficientHomotopy f).level n (r, x)) := rfl

/-- The actual cone-cylinder square supplies its genuine pasted boundary comparison. -/
def boundedFlatBassSourceLegConeBoundary := (boundedFlatBassSourceLegConeSquare f).toBoundary

end Quillen.PerfectComplexes
