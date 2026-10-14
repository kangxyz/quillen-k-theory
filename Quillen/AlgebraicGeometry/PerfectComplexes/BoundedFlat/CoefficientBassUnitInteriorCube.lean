/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitCharts
public import Quillen.Topology.Prespectrum.PushoutSquareFilling

/-! The remaining six-face identity cube for the constructed original polynomial-span unit.
This controlled sufficient route does not claim necessity for every Bass cone identity. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The live interior obligation retains the fixed original Bass homotopy and all six faces.
Both chart squares and the whole span identity in this type are already constructed. -/
abbrev BoundedFlatCoefficientBassIdentityInteriorCube (a : Under R) :=
  HomotopyPushout.SquareCylinder
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientBassComparisonHomotopy P (𝟙 a))
    (coneSquareIdentityTrack (boundedFlatCoefficientBassSquareComparison P a))
    (Homotopy.precomp (boundedFlatCoefficientBassSquareComparison P a)
      (boundedFlatCoefficientLaurentIdentityHomotopy P a))
    ((boundedFlatCoefficientPolynomialSpanIdentityHomotopy P a).postcomp
      (boundedFlatCoefficientBassSquareComparison P a))
    (boundedFlatCoefficientBassIdentityPlusChart P a)
    (boundedFlatCoefficientBassIdentityMinusChart P a)

/-- A future genuine producer of this cube completes the exact original Bass identity square. -/
def boundedFlatCoefficientBassComparisonIdentitySquareOfInteriorCube (a : Under R)
    (Q : BoundedFlatCoefficientBassIdentityInteriorCube P a) :
    BoundedFlatCoefficientBassComparisonIdentitySquare P a
      (boundedFlatCoefficientPolynomialSpanIdentityHomotopy P a) :=
  HomotopyPushout.squareOfCylinder _ _ _ _ _ _ _ _ Q

/-- Quotient descent retains all three independent coordinates of the supplied interior. -/
theorem boundedFlatCoefficientBassComparisonIdentitySquareOfInteriorCube_cylinder (a : Under R)
    (Q : BoundedFlatCoefficientBassIdentityInteriorCube P a)
    (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassComparisonIdentitySquareOfInteriorCube P a Q).level n
      (r, (s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x))) =
      Q.level n (r, (s, (t, x))) := rfl

end Quillen.PerfectComplexes
