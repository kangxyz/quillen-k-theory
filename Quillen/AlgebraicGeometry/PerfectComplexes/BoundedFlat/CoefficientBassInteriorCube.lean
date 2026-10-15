/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Topology.Prespectrum.PushoutSquareFilling
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositionCharts
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassWholeLawCriterion

/-!
# Coefficient Bass Interior Cube

The precise remaining ORIGINAL native coefficient composition cube and its complete consumer.
Both chart squares are constructed. The cube itself remains an unconstructed obligation here.

This six-face cube is sufficient for the selected chart-preserving construction; necessity for
every possible cone law is not asserted.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The exact remaining six-faced cylinder cube for the fixed original raw composition law.
Its two chart faces are the already CONSTRUCTED native plus/minus rectangles. -/
abbrev BoundedFlatCoefficientBassCompositionInteriorCube :=
  HomotopyPushout.SquareCylinder
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientBassComparisonHomotopy P (u ≫ v))
    (boundedFlatCoefficientBassCompositeComparison P u v)
    (Homotopy.precomp (boundedFlatCoefficientBassSquareComparison P a)
      (boundedFlatCoefficientLaurentCompositionHomotopy P u v))
    ((boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v).postcomp
      (boundedFlatCoefficientBassSquareComparison P c))
    (boundedFlatCoefficientBassCompositionPlusChart P u v)
    (boundedFlatCoefficientBassCompositionMinusChart P u v)

/-- A genuine producer of the six-faced cube completes the whole ORIGINAL comparison square. -/
def boundedFlatCoefficientBassComparisonSquareOfInteriorCube
    (Q : BoundedFlatCoefficientBassCompositionInteriorCube P u v) :
    BoundedFlatCoefficientBassComparisonCompositionSquare P u v :=
  HomotopyPushout.squareOfCylinder _ _ _ _ _ _ _ _ Q

/-- The entire original positive-chart square is retained pointwise. -/
theorem boundedFlatCoefficientBassComparisonSquareOfInteriorCube_inl
    (Q : BoundedFlatCoefficientBassCompositionInteriorCube P u v)
    (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassComparisonSquareOfInteriorCube P u v Q).level n
      (r, (s, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) =
      (boundedFlatCoefficientBassCompositionPlusChart P u v).level n (r, (s, x)) := rfl

/-- The separate original inverse-coordinate chart square is retained pointwise. -/
theorem boundedFlatCoefficientBassComparisonSquareOfInteriorCube_inr
    (Q : BoundedFlatCoefficientBassCompositionInteriorCube P u v)
    (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassComparisonSquareOfInteriorCube P u v Q).level n
      (r, (s, (HomotopyPushout.inr
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) =
      (boundedFlatCoefficientBassCompositionMinusChart P u v).level n (r, (s, x)) := rfl

/-- The prescribed inner cube survives quotient descent with all three times independent. -/
theorem boundedFlatCoefficientBassComparisonSquareOfInteriorCube_cylinder
    (Q : BoundedFlatCoefficientBassCompositionInteriorCube P u v)
    (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassComparisonSquareOfInteriorCube P u v Q).level n
      (r, (s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x))) =
      Q.level n (r, (s, (t, x))) := rfl

/-- Conditional WHOLE composition for the original cone maps, consuming the concrete native cube. -/
def boundedFlatCoefficientBassConeCompositionOfInteriorCube
    (Q : BoundedFlatCoefficientBassCompositionInteriorCube P u v) :
    Homotopy (boundedFlatCoefficientBassConeMap P (u ≫ v))
      (boundedFlatCoefficientBassConeMap P u ≫ boundedFlatCoefficientBassConeMap P v) :=
  boundedFlatCoefficientBassConeCompositionOfComparisonSquare P u v
    (boundedFlatCoefficientBassComparisonSquareOfInteriorCube P u v Q)

/-- The fixed original Laurent composition track survives unchanged through both descents. -/
theorem boundedFlatCoefficientBassConeCompositionOfInteriorCube_inclusion
    (Q : BoundedFlatCoefficientBassCompositionInteriorCube P u v)
    (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v Q).level n
      (r, (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n x) =
        (boundedFlatCoefficientBassConeCompositionInclusionHomotopy P u v).level n (r, x) := rfl

/-- Both original quotient constructions and parameter looping are now explicit consumers.
Producing the displayed `Q` remains necessary for using this as a native composition law. -/
def boundedFlatCoefficientBassStepCompositionOfInteriorCube
    (Q : BoundedFlatCoefficientBassCompositionInteriorCube P u v) :
    Homotopy (boundedFlatCoefficientBassStepMap P (u ≫ v))
      (boundedFlatCoefficientBassStepMap P u ≫ boundedFlatCoefficientBassStepMap P v) :=
  (boundedFlatCoefficientBassConeCompositionOfInteriorCube P u v Q).parameterLooping.cast
    rfl (parameterLoopingFunctor.map_comp _ _)

end Quillen.PerfectComplexes
