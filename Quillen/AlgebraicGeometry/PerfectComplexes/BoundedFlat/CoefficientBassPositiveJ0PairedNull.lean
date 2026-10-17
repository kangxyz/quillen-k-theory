/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Path.RetypedConeNullComparison
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0Rectangles

/-!
# Separate ordinary and shifted carrier null comparisons

The full polynomial seams retype cone endpoints. Both actual square interiors and every
binary comparison clock are retained. Native identification with originalNullComparison,
its ofLevels transports, and the final two-sheet unit conjugation remain separate.
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
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0PairedNull
open CommonReferenceNerve CoefficientBassPositiveJ0ConeBoundaries
open CoefficientBassPositiveJ0Rectangles
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- The minus old cone has the rectangle rail's exact source type. -/
abbrev oldConeMinus := (coneSquareMinus P d).rebaseOld
  (polynomialMovementMinus P d) (polynomialMinus_seam P d)

/-- The minus new cone retains its own original tip. -/
abbrev newConeMinus := (coneSquareMinus P d).rebaseNew
  (polynomialMovementMinus P d) (polynomialMinus_seam P d)

/-- The complete original square, with its lower rail named by the actual rectangle. -/
abbrev coneSquareTypedMinus := (coneSquareMinus P d).rebaseMovement
  (polynomialMovementMinus P d) (polynomialMinus_seam P d)

/-- The actual collapse followed by the unchanged terminal-pause cancellation. -/
def coneComparisonMinus : (oldConeMinus P d).Homotopy
    ((polynomialMovementMinus P d).trans (newConeMinus P d)) :=
  (coneSquareTypedMinus P d).coneBoundary

/-- Endpoint retyping leaves the entire cone comparison unchanged. -/
theorem coneComparisonMinus_apply (r s : I) :
    coneComparisonMinus P d (r, s) = coneBoundaryMinus P d (r, s) :=
  (coneSquareMinus P d).rebaseMovement_coneBoundary_apply
    (polynomialMovementMinus P d) (polynomialMinus_seam P d) r s

/-- The literal old null word has the original two nested path subdivisions. -/
abbrev oldNullMinus := (oldPositiveMinus P d).trans
  ((positiveMovementMinus P d).trans (oldConeMinus P d))

/-- The literal new null word retains the separate minus tip. -/
abbrev newNullMinus := (newPositiveMinus P d).trans (newConeMinus P d)

/-- Original straight-positive word applied to this actual full rectangle. -/
def straightPositiveMinus :
    (((oldPositiveMinus P d).trans (positiveMovementMinus P d)).trans
      (polynomialMovementMinus P d)).Homotopy
        ((laurentMovementMinus P d).trans (newPositiveMinus P d)) :=
  Path.Homotopy.straightPositiveWord (oldPositiveMinus P d)
    (positiveMovementMinus P d) (polynomialMovementMinus P d)
    (laurentMovementMinus P d) (newPositiveMinus P d) (rectangleMinus P d)

/-- The minus paired-null constituent uses the literal original five-stage recipe. -/
def pastedNullMinus : (oldNullMinus P d).Homotopy
    ((laurentMovementMinus P d).trans (newNullMinus P d)) :=
  Path.Homotopy.pastedPositiveNullWord (oldPositiveMinus P d)
    (positiveMovementMinus P d) (polynomialMovementMinus P d)
    (laurentMovementMinus P d) (newPositiveMinus P d)
    (oldConeMinus P d) (newConeMinus P d) (rectangleMinus P d)
    (coneComparisonMinus P d)

/-- The plus old cone has the rectangle rail's exact source type. -/
abbrev oldConePlus := (coneSquarePlus P d).rebaseOld
  (polynomialMovementPlus P d) (polynomialPlus_seam P d)

/-- The plus new cone retains its own original tip. -/
abbrev newConePlus := (coneSquarePlus P d).rebaseNew
  (polynomialMovementPlus P d) (polynomialPlus_seam P d)

/-- The complete original square, with its lower rail named by the actual rectangle. -/
abbrev coneSquareTypedPlus := (coneSquarePlus P d).rebaseMovement
  (polynomialMovementPlus P d) (polynomialPlus_seam P d)

/-- The actual collapse followed by the unchanged terminal-pause cancellation. -/
def coneComparisonPlus : (oldConePlus P d).Homotopy
    ((polynomialMovementPlus P d).trans (newConePlus P d)) :=
  (coneSquareTypedPlus P d).coneBoundary

/-- Endpoint retyping leaves the entire cone comparison unchanged. -/
theorem coneComparisonPlus_apply (r s : I) :
    coneComparisonPlus P d (r, s) = coneBoundaryPlus P d (r, s) :=
  (coneSquarePlus P d).rebaseMovement_coneBoundary_apply
    (polynomialMovementPlus P d) (polynomialPlus_seam P d) r s

/-- The literal old null word has the original two nested path subdivisions. -/
abbrev oldNullPlus := (oldPositivePlus P d).trans
  ((positiveMovementPlus P d).trans (oldConePlus P d))

/-- The literal new null word retains the separate plus tip. -/
abbrev newNullPlus := (newPositivePlus P d).trans (newConePlus P d)

/-- Original straight-positive word applied to this actual full rectangle. -/
def straightPositivePlus :
    (((oldPositivePlus P d).trans (positiveMovementPlus P d)).trans
      (polynomialMovementPlus P d)).Homotopy
        ((laurentMovementPlus P d).trans (newPositivePlus P d)) :=
  Path.Homotopy.straightPositiveWord (oldPositivePlus P d)
    (positiveMovementPlus P d) (polynomialMovementPlus P d)
    (laurentMovementPlus P d) (newPositivePlus P d) (rectanglePlus P d)

/-- The plus paired-null constituent uses the literal original five-stage recipe. -/
def pastedNullPlus : (oldNullPlus P d).Homotopy
    ((laurentMovementPlus P d).trans (newNullPlus P d)) :=
  Path.Homotopy.pastedPositiveNullWord (oldPositivePlus P d)
    (positiveMovementPlus P d) (polynomialMovementPlus P d)
    (laurentMovementPlus P d) (newPositivePlus P d)
    (oldConePlus P d) (newConePlus P d) (rectanglePlus P d)
    (coneComparisonPlus P d)

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0PairedNull
