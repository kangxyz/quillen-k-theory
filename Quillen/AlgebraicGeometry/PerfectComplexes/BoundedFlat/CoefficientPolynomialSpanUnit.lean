/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientPolynomialUnit
public import Quillen.Topology.Prespectrum.PushoutIdentityFromUnitSquare

/-! The controlled identity of the whole original coefficient polynomial span. -/

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

/-- The whole original overlap square, including both chart edges and the actual final cylinder. -/
def boundedFlatCoefficientPolynomialSpanIdentityCylinderSquare (a : Under R) :=
  HomotopyPushout.identicalLegIdentityCylinderSquare
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientPolynomialSquareHomotopy P (𝟙 a))
    (boundedFlatCoefficientIdentityHomotopy P a)
    (boundedFlatCoefficientPolynomialIdentityHomotopy P a)
    (boundedFlatCoefficientPolynomialIdentitySquare P a)

/-- The whole ORIGINAL polynomial-span map has its controlled identity homotopy. -/
def boundedFlatCoefficientPolynomialSpanIdentityHomotopy (a : Under R) :
    Homotopy (boundedFlatCoefficientPolynomialSpanMap P (𝟙 a))
      (𝟙 (HomotopyPushout.prespectrum
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)))) :=
  HomotopyPushout.identicalLegIdentityHomotopy
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientPolynomialSquareHomotopy P (𝟙 a))
    (boundedFlatCoefficientIdentityHomotopy P a)
    (boundedFlatCoefficientPolynomialIdentityHomotopy P a)
    (boundedFlatCoefficientPolynomialIdentitySquare P a)

/-- The full positive chart is exactly the prescribed original polynomial unit track. -/
theorem boundedFlatCoefficientPolynomialSpanIdentityHomotopy_inl (a : Under R)
    (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientPolynomialSpanIdentityHomotopy P a).level n
      (r, (HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x) =
      (HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n
          ((boundedFlatCoefficientPolynomialIdentityHomotopy P a).level n (r, x)) := rfl

/-- The full negative chart is exactly the same original polynomial unit track. -/
theorem boundedFlatCoefficientPolynomialSpanIdentityHomotopy_inr (a : Under R)
    (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientPolynomialSpanIdentityHomotopy P a).level n
      (r, (HomotopyPushout.inr (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x) =
      (HomotopyPushout.inr (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n
          ((boundedFlatCoefficientPolynomialIdentityHomotopy P a).level n (r, x)) := rfl

/-- Every cylinder point retains the full constructed square in two independent parameters. -/
theorem boundedFlatCoefficientPolynomialSpanIdentityHomotopy_cylinder (a : Under R)
    (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientPolynomialSpanIdentityHomotopy P a).level n
      (r, HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (s, x)) =
      (boundedFlatCoefficientPolynomialSpanIdentityCylinderSquare P a).level n (r, (s, x)) := rfl

end Quillen.PerfectComplexes
