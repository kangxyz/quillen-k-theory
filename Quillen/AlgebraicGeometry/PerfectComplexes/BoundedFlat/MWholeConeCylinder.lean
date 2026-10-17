/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeCubeConsumers

/-! The complete moving null square used by the chosen original cone composition track.
This retains the existing geometric square, interchange, boundary collapse, reassociation,
and square descent. In particular, the cone-cylinder value is not replaced by the bare M cube.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWhole
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The exact constructed moving null square, including its original three-side conversions. -/
def compositionNullSquare :=
  coneSquareCompositionMovingNullSquare
    (boundedFlatCoefficientBassSquareComparison P a)
    (boundedFlatCoefficientBassSquareComparison P b)
    (boundedFlatCoefficientBassSquareComparison P c)
    (boundedFlatCoefficientPolynomialSpanMap P u)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedFlatCoefficientPolynomialSpanMap P v)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map v)))
    (boundedFlatCoefficientBassComparisonHomotopy P u)
    (boundedFlatCoefficientBassComparisonHomotopy P v)
    (boundedFlatCoefficientBassComparisonHomotopy P (u ≫ v))
    (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v)
    (boundedFlatCoefficientLaurentCompositionHomotopy P u v) (comparisonSquare P u v)

/-- Every whole cone-cylinder point retains this null square at its two independent times. -/
theorem cone_cylinder (n : ℕ) (r s : unitInterval)
    (x : (HomotopyPushout.prespectrum
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).space n) :
    (coneComposition P u v).level n
      (r, (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a)).level n
        (s, x)) = (compositionNullSquare P u v).level n (r, (s, x)) := rfl

end Quillen.PerfectComplexes.BassMWhole
