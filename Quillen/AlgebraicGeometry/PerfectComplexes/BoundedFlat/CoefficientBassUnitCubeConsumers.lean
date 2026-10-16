/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitNativeCube

/-! The original whole comparison, cone, and parameter-looped unit laws
from the constructed cube. -/

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
namespace Quillen.PerfectComplexes.CoefficientBassUnitCubeConsumers
open CoefficientBassUnitNativeCube
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The entire original comparison square has the constructed six-faced interior. -/
def comparisonSquare : BoundedFlatCoefficientBassComparisonIdentitySquare P a
    (boundedFlatCoefficientPolynomialSpanIdentityHomotopy P a) :=
  boundedFlatCoefficientBassComparisonIdentitySquareOfInteriorCube P a (interiorCube P a)

/-- The whole original cone identity needs no supplied filler or compatibility assumption. -/
def coneIdentity : Homotopy (boundedFlatCoefficientBassConeMap P (𝟙 a))
    (𝟙 (mappingCone (boundedFlatCoefficientBassSquareComparison P a))) :=
  boundedFlatCoefficientBassConeIdentityOfComparisonSquare P a
    (boundedFlatCoefficientPolynomialSpanIdentityHomotopy P a) (comparisonSquare P a)

/-- Parameter looping retains the complete original unit law at every native level. -/
def stepIdentity : Homotopy (boundedFlatCoefficientBassStepMap P (𝟙 a))
    (𝟙 (parameterLooping (mappingCone (boundedFlatCoefficientBassSquareComparison P a)))) :=
  boundedFlatCoefficientBassStepIdentityOfComparisonSquare P a
    (boundedFlatCoefficientPolynomialSpanIdentityHomotopy P a) (comparisonSquare P a)

/-- The distinct original positive chart is preserved by the actual quotient descent. -/
theorem comparison_inl (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (comparisonSquare P a).level n
      (r, (s, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) =
      (boundedFlatCoefficientBassIdentityPlusChart P a).level n (r, (s, x)) := rfl

/-- The inverse-coordinate chart retains its own entire original native square. -/
theorem comparison_inr (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (comparisonSquare P a).level n
      (r, (s, (HomotopyPushout.inr
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) =
      (boundedFlatCoefficientBassIdentityMinusChart P a).level n (r, (s, x)) := rfl

/-- All three independent scalar coordinates survive the complete original cylinder quotient. -/
theorem comparison_cylinder (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (comparisonSquare P a).level n
      (r, (s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x))) =
      (interiorCube P a).level n (r, (s, (t, x))) := rfl

/-- The original Laurent identity track survives both quotient descents without replacement. -/
theorem cone_inclusion (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    (coneIdentity P a).level n
      (r, (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n x) =
      (boundedFlatCoefficientBassConeIdentityInclusionHomotopy P a).level n (r, x) :=
  boundedFlatCoefficientBassConeIdentityOfComparisonSquare_inclusion P a
    (boundedFlatCoefficientPolynomialSpanIdentityHomotopy P a) (comparisonSquare P a) n r x

end Quillen.PerfectComplexes.CoefficientBassUnitCubeConsumers
