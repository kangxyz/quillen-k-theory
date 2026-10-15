/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientPolynomialSpanUnit

/-! Complete chart faces for the subsequent ORIGINAL Bass comparison identity square. -/

@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- Identifying the two geometric identity arrows preserves the entire original square track. -/
theorem boundedFlatPerfectPrespectrumSquareHomotopy_geometricIdentity_level
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ X) (w : Y ⟶ Y)
    (ep : p = 𝟙 X) (ew : w = 𝟙 Y) (h : p ≫ f = f ≫ w) (n : ℕ) :
    (boundedFlatPerfectPrespectrumSquareHomotopy p f f w h).level n =
      (boundedFlatPerfectPrespectrumSquareHomotopy (𝟙 X) f f (𝟙 Y) (by simp)).level n := by
  subst p
  subst w
  rfl

/-- The positive Laurent chart has its actual unit square with both original coefficient units. -/
def boundedFlatCoefficientPlusIdentitySquare (a : Under R) :
    (boundedFlatCoefficientPlusSquareHomotopy P (𝟙 a)).Square
      (coneSquareIdentityTrack (boundedFlatPerfectPrespectrumMap (laurentPlus P a)))
      (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (laurentPlus P a))
        (boundedFlatCoefficientLaurentIdentityHomotopy P a))
      ((boundedFlatCoefficientPolynomialIdentityHomotopy P a).postcomp
        (boundedFlatPerfectPrespectrumMap (laurentPlus P a))) := by
  refine (boundedFlatPerfectPrespectrumUnitSquare (laurentPlus P a)).ofBoundaryLevels
    _ _ _ _ ?_ (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  intro n
  exact boundedFlatPerfectPrespectrumSquareHomotopy_geometricIdentity_level _ _ _
    ((congrArg (coefficientMap P) ((laurentUnderFunctor R).map_id a)).trans
      (boundedFlatCoefficientGeometricIdentity P ((laurentUnderFunctor R).obj a)))
    ((congrArg (coefficientMap P) ((polynomialUnderFunctor R).map_id a)).trans
      (boundedFlatCoefficientGeometricIdentity P ((polynomialUnderFunctor R).obj a))) _ n

/-- The inverse-coordinate chart has its separate original unit square. -/
def boundedFlatCoefficientMinusIdentitySquare (a : Under R) :
    (boundedFlatCoefficientMinusSquareHomotopy P (𝟙 a)).Square
      (coneSquareIdentityTrack (boundedFlatPerfectPrespectrumMap (laurentMinus P a)))
      (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (laurentMinus P a))
        (boundedFlatCoefficientLaurentIdentityHomotopy P a))
      ((boundedFlatCoefficientPolynomialIdentityHomotopy P a).postcomp
        (boundedFlatPerfectPrespectrumMap (laurentMinus P a))) := by
  refine (boundedFlatPerfectPrespectrumUnitSquare (laurentMinus P a)).ofBoundaryLevels
    _ _ _ _ ?_ (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  intro n
  exact boundedFlatPerfectPrespectrumSquareHomotopy_geometricIdentity_level _ _ _
    ((congrArg (coefficientMap P) ((laurentUnderFunctor R).map_id a)).trans
      (boundedFlatCoefficientGeometricIdentity P ((laurentUnderFunctor R).obj a)))
    ((congrArg (coefficientMap P) ((polynomialUnderFunctor R).map_id a)).trans
      (boundedFlatCoefficientGeometricIdentity P ((polynomialUnderFunctor R).obj a))) _ n

/-- The exact chart restriction of the remaining Bass square for the constructed span identity. -/
abbrev BoundedFlatCoefficientBassIdentityChartSquare (a : Under R)
    (i : originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a))) ⟶
        HomotopyPushout.prespectrum
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))) :=
  (Homotopy.precomp i (boundedFlatCoefficientBassComparisonHomotopy P (𝟙 a))).Square
    (Homotopy.precomp i
      (coneSquareIdentityTrack (boundedFlatCoefficientBassSquareComparison P a)))
    (Homotopy.precomp i
      (Homotopy.precomp (boundedFlatCoefficientBassSquareComparison P a)
        (boundedFlatCoefficientLaurentIdentityHomotopy P a)))
    (Homotopy.precomp i
      ((boundedFlatCoefficientPolynomialSpanIdentityHomotopy P a).postcomp
        (boundedFlatCoefficientBassSquareComparison P a)))

/-- The complete positive chart of the next Bass identity square is constructed. -/
def boundedFlatCoefficientBassIdentityPlusChart (a : Under R) :
    BoundedFlatCoefficientBassIdentityChartSquare P a
      (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))) :=
  (boundedFlatCoefficientPlusIdentitySquare P a).ofBoundaryLevels _ _ _ _
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- The complete inverse-coordinate chart of the next Bass identity square is constructed. -/
def boundedFlatCoefficientBassIdentityMinusChart (a : Under R) :
    BoundedFlatCoefficientBassIdentityChartSquare P a
      (HomotopyPushout.inr
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))) :=
  (boundedFlatCoefficientMinusIdentitySquare P a).ofBoundaryLevels _ _ _ _
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

end Quillen.PerfectComplexes
