/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftConeSquares
public import Quillen.Aglib.Topology.Path.MappedProjectionRectangle
/-!
# The two original finite positive rectangles for the left route

Each ordinary and shifted rectangle is mapped through its actual 31-node characteristic map.
All five scalar rails retain their original clocks. The polynomial rail is identified with
its own A or B square before native evaluation, with the two tips still distinct.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftRectangles
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierSeed CoefficientBassPositiveLeftCellParameters
open CoefficientBassPositiveLeftConeSquares
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The actual first full-reference rectangle, on the specified sheet. -/
def firstMap (e : Bool) : C(StdSimplex ℝ (Fin 31), Carrier P p q) :=
  (includeLaurent P p q).comp
    (parameter (laurentReference P p q) (firstRectangleNodes P p q e))

/-- The unchanged first D rail. -/
abbrev firstOldPositive (e : Bool) :=
  (ProjectionRectangleParameters.D BassH0Diagram.plusFace).map
    (firstMap P p q e).continuous

/-- The unchanged first L rail. -/
abbrev firstPositiveMovement (e : Bool) :=
  (ProjectionRectangleParameters.L BassH0Diagram.plusFace).map
    (firstMap P p q e).continuous

/-- The unchanged first Ppath rail. -/
abbrev firstPolynomialMovement (e : Bool) :=
  (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace).map
    (firstMap P p q e).continuous

/-- The unchanged first T rail. -/
abbrev firstLaurentMovement (e : Bool) :=
  (ProjectionRectangleParameters.T BassH0Diagram.plusFace).map
    (firstMap P p q e).continuous

/-- The unchanged first K rail. -/
abbrev firstNewPositive (e : Bool) :=
  (ProjectionRectangleParameters.K BassH0Diagram.plusFace).map
    (firstMap P p q e).continuous

/-- The unchanged positive-pasting comparison on the first constituent. -/
def firstRectangle (e : Bool) :
    ((firstPositiveMovement P p q e).trans
      (firstPolynomialMovement P p q e)).Homotopy
    ((firstOldPositive P p q e).symm.trans
      ((firstLaurentMovement P p q e).trans (firstNewPositive P p q e))) :=
  Path.Homotopy.mapProjectionRectangle (firstMap P p q e)
    (ProjectionRectangleParameters.D BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.L BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.T BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.K BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace)

/-- Neither rectangle coordinate is reparameterized. -/
theorem first_rectangle_apply (e : Bool) (r s : I) :
    firstRectangle P p q e (r, s) = firstMap P p q e
      (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace (r, s)) := rfl

/-- The complete polynomial rail is the exact lower edge of its own A square. -/
theorem first_polynomial_seam (e : Bool) (s : I) :
    firstPolynomialMovement P p q e s = (ASquare P p q e).parameter (s, 0) := by
  change includeLaurent P p q (firstMovement P p q e s) =
    A P p q e (s, 0)
  exact (A_left P p q e s).symm

/-- The actual middle full-reference rectangle, on the specified sheet. -/
def middleMap (e : Bool) : C(StdSimplex ℝ (Fin 31), Carrier P p q) :=
  (includeLaurent P p q).comp
    (parameter (laurentReference P p q) (middleRectangleNodes P p q e))

/-- The unchanged middle D rail. -/
abbrev middleOldPositive (e : Bool) :=
  (ProjectionRectangleParameters.D BassH0Diagram.plusFace).map
    (middleMap P p q e).continuous

/-- The unchanged middle L rail. -/
abbrev middlePositiveMovement (e : Bool) :=
  (ProjectionRectangleParameters.L BassH0Diagram.plusFace).map
    (middleMap P p q e).continuous

/-- The unchanged middle Ppath rail. -/
abbrev middlePolynomialMovement (e : Bool) :=
  (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace).map
    (middleMap P p q e).continuous

/-- The unchanged middle T rail. -/
abbrev middleLaurentMovement (e : Bool) :=
  (ProjectionRectangleParameters.T BassH0Diagram.plusFace).map
    (middleMap P p q e).continuous

/-- The unchanged middle K rail. -/
abbrev middleNewPositive (e : Bool) :=
  (ProjectionRectangleParameters.K BassH0Diagram.plusFace).map
    (middleMap P p q e).continuous

/-- The unchanged positive-pasting comparison on the middle constituent. -/
def middleRectangle (e : Bool) :
    ((middlePositiveMovement P p q e).trans
      (middlePolynomialMovement P p q e)).Homotopy
    ((middleOldPositive P p q e).symm.trans
      ((middleLaurentMovement P p q e).trans (middleNewPositive P p q e))) :=
  Path.Homotopy.mapProjectionRectangle (middleMap P p q e)
    (ProjectionRectangleParameters.D BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.L BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.T BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.K BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace)

/-- Neither rectangle coordinate is reparameterized. -/
theorem middle_rectangle_apply (e : Bool) (r s : I) :
    middleRectangle P p q e (r, s) = middleMap P p q e
      (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace (r, s)) := rfl

/-- The complete polynomial rail is the exact lower edge of its own B square. -/
theorem middle_polynomial_seam (e : Bool) (s : I) :
    middlePolynomialMovement P p q e s = (BSquare P p q e).parameter (s, 0) := by
  change includeLaurent P p q (secondMovement P p q e s) =
    B P p q e (s, 0)
  exact (B_left P p q e s).symm

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftRectangles
