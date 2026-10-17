/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftPairedNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftUnitPasting
public import Quillen.Aglib.Topology.Path.TwoSheetConjugation
/-!
# The actual first and middle left-route comparisons

The two finite positive rectangles, their original unit pastings, and their separately tipped
cone squares supply the literal two-sheet comparison. No comparison or endpoint seed is assumed.
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
namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftComparisons
open CoefficientBassPositiveLeftRectangles CoefficientBassPositiveLeftPairedNull
open CoefficientBassPositiveLeftUnitPasting
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The original old seed word for the first constituent. -/
abbrev firstSourceWord := (firstOldNull P p q false).symm.trans
  ((firstOldUnit P p q).trans (firstOldNull P p q true))

/-- The original new seed word for the first constituent. -/
abbrev firstTargetWord := (firstNewNull P p q false).symm.trans
  ((firstNewUnit P p q).trans (firstNewNull P p q true))

/-- The literal two-sheet conjugation on the actual first finite families. -/
def firstComparison : (firstSourceWord P p q).Homotopy (firstTargetWord P p q) :=
  Path.Homotopy.TwoSheetConjugation.comparison (firstOldUnit P p q) (firstNewUnit P p q)
    (firstLaurentMovement P p q false) (firstLaurentMovement P p q true)
    (firstOldNull P p q false) (firstOldNull P p q true)
    (firstNewNull P p q false) (firstNewNull P p q true)
    (firstUnitComparison P p q) (firstPastedNull P p q false)
    (firstPastedNull P p q true)

/-- The original old seed word for the middle constituent. -/
abbrev middleSourceWord := (middleOldNull P p q false).symm.trans
  ((middleOldUnit P p q).trans (middleOldNull P p q true))

/-- The original new seed word for the middle constituent. -/
abbrev middleTargetWord := (middleNewNull P p q false).symm.trans
  ((middleNewUnit P p q).trans (middleNewNull P p q true))

/-- The literal two-sheet conjugation on the actual middle finite families. -/
def middleComparison : (middleSourceWord P p q).Homotopy (middleTargetWord P p q) :=
  Path.Homotopy.TwoSheetConjugation.comparison (middleOldUnit P p q) (middleNewUnit P p q)
    (middleLaurentMovement P p q false) (middleLaurentMovement P p q true)
    (middleOldNull P p q false) (middleOldNull P p q true)
    (middleNewNull P p q false) (middleNewNull P p q true)
    (middleUnitComparison P p q) (middlePastedNull P p q false)
    (middlePastedNull P p q true)

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftComparisons
