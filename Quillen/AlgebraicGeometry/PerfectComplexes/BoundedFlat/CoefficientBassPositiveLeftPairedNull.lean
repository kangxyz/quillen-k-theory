/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftRectangles
public import Quillen.Topology.Path.RetypedConeNullComparison

/-!
# Actual paired null comparisons for both left-route constituents

Each square is rebased only along the proved whole polynomial rail. The original five-stage
positive-null recipe then gives the actual comparison, retaining the specified sheet's tip.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftPairedNull
open CoefficientBassPositiveLeftConeSquares (ASquare BSquare firstLowerPath secondLowerPath)
open CoefficientBassPositiveLeftRectangles
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The full first lower rail, with the square's actual boundary path type. -/
theorem first_lower_seam (e : Bool) (s : I) :
    firstPolynomialMovement P p q e s = firstLowerPath P p q e s :=
  (first_polynomial_seam P p q e s).trans ((ASquare P p q e).left s)

/-- The full middle lower rail, with the square's actual boundary path type. -/
theorem middle_lower_seam (e : Bool) (s : I) :
    middlePolynomialMovement P p q e s = secondLowerPath P p q e s :=
  (middle_polynomial_seam P p q e s).trans ((BSquare P p q e).left s)

/-- The first OldCone uses the exact polynomial-rail endpoint types. -/
abbrev firstOldCone (e : Bool) := (ASquare P p q e).rebaseOld
  (firstPolynomialMovement P p q e) (first_lower_seam P p q e)

/-- The first NewCone uses the exact polynomial-rail endpoint types. -/
abbrev firstNewCone (e : Bool) := (ASquare P p q e).rebaseNew
  (firstPolynomialMovement P p q e) (first_lower_seam P p q e)

/-- The first ConeSquare uses the exact polynomial-rail endpoint types. -/
abbrev firstConeSquare (e : Bool) := (ASquare P p q e).rebaseMovement
  (firstPolynomialMovement P p q e) (first_lower_seam P p q e)

/-- The original collapse and terminal-pause cancellation of the first square. -/
def firstConeComparison (e : Bool) : (firstOldCone P p q e).Homotopy
    ((firstPolynomialMovement P p q e).trans (firstNewCone P p q e)) :=
  (firstConeSquare P p q e).coneBoundary

/-- Retyping does not change either time of the square boundary comparison. -/
theorem first_cone_comparison_apply (e : Bool) (r s : I) :
    firstConeComparison P p q e (r, s) = (ASquare P p q e).coneBoundary (r, s) :=
  (ASquare P p q e).rebaseMovement_coneBoundary_apply
    (firstPolynomialMovement P p q e) (first_lower_seam P p q e) r s

/-- The literal original old null, with both nested half clocks. -/
abbrev firstOldNull (e : Bool) := (firstOldPositive P p q e).trans
  ((firstPositiveMovement P p q e).trans (firstOldCone P p q e))

/-- The literal original new null, at the same sheet's own tip. -/
abbrev firstNewNull (e : Bool) :=
  (firstNewPositive P p q e).trans (firstNewCone P p q e)

/-- The actual original five-stage positive-null comparison. -/
def firstPastedNull (e : Bool) : (firstOldNull P p q e).Homotopy
    ((firstLaurentMovement P p q e).trans (firstNewNull P p q e)) :=
  Path.Homotopy.pastedPositiveNullWord (firstOldPositive P p q e)
    (firstPositiveMovement P p q e) (firstPolynomialMovement P p q e)
    (firstLaurentMovement P p q e) (firstNewPositive P p q e)
    (firstOldCone P p q e) (firstNewCone P p q e) (firstRectangle P p q e)
    (firstConeComparison P p q e)

/-- The middle OldCone uses the exact polynomial-rail endpoint types. -/
abbrev middleOldCone (e : Bool) := (BSquare P p q e).rebaseOld
  (middlePolynomialMovement P p q e) (middle_lower_seam P p q e)

/-- The middle NewCone uses the exact polynomial-rail endpoint types. -/
abbrev middleNewCone (e : Bool) := (BSquare P p q e).rebaseNew
  (middlePolynomialMovement P p q e) (middle_lower_seam P p q e)

/-- The middle ConeSquare uses the exact polynomial-rail endpoint types. -/
abbrev middleConeSquare (e : Bool) := (BSquare P p q e).rebaseMovement
  (middlePolynomialMovement P p q e) (middle_lower_seam P p q e)

/-- The original collapse and terminal-pause cancellation of the middle square. -/
def middleConeComparison (e : Bool) : (middleOldCone P p q e).Homotopy
    ((middlePolynomialMovement P p q e).trans (middleNewCone P p q e)) :=
  (middleConeSquare P p q e).coneBoundary

/-- Retyping does not change either time of the square boundary comparison. -/
theorem middle_cone_comparison_apply (e : Bool) (r s : I) :
    middleConeComparison P p q e (r, s) = (BSquare P p q e).coneBoundary (r, s) :=
  (BSquare P p q e).rebaseMovement_coneBoundary_apply
    (middlePolynomialMovement P p q e) (middle_lower_seam P p q e) r s

/-- The literal original old null, with both nested half clocks. -/
abbrev middleOldNull (e : Bool) := (middleOldPositive P p q e).trans
  ((middlePositiveMovement P p q e).trans (middleOldCone P p q e))

/-- The literal original new null, at the same sheet's own tip. -/
abbrev middleNewNull (e : Bool) :=
  (middleNewPositive P p q e).trans (middleNewCone P p q e)

/-- The actual original five-stage positive-null comparison. -/
def middlePastedNull (e : Bool) : (middleOldNull P p q e).Homotopy
    ((middleLaurentMovement P p q e).trans (middleNewNull P p q e)) :=
  Path.Homotopy.pastedPositiveNullWord (middleOldPositive P p q e)
    (middlePositiveMovement P p q e) (middlePolynomialMovement P p q e)
    (middleLaurentMovement P p q e) (middleNewPositive P p q e)
    (middleOldCone P p q e) (middleNewCone P p q e) (middleRectangle P p q e)
    (middleConeComparison P p q e)

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftPairedNull
