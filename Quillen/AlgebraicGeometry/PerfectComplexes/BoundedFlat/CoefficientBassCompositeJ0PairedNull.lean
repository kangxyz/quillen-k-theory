/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Path.RetypedConeNullComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0Rectangles

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
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0PairedNull
open CommonReferenceNerve CoefficientBassCompositeJ0ConeBoundaries
open CoefficientBassCompositeJ0Rectangles
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The minus old cone has the rectangle rail's exact source type. -/
abbrev oldConeMinus := (coneSquareMinus P p q).rebaseOld
  (polynomialMovementMinus P p q) (polynomialMinus_seam P p q)

/-- The minus new cone retains its own original tip. -/
abbrev newConeMinus := (coneSquareMinus P p q).rebaseNew
  (polynomialMovementMinus P p q) (polynomialMinus_seam P p q)

/-- The complete original square, with its lower rail named by the actual rectangle. -/
abbrev coneSquareTypedMinus := (coneSquareMinus P p q).rebaseMovement
  (polynomialMovementMinus P p q) (polynomialMinus_seam P p q)

/-- The actual collapse followed by the unchanged terminal-pause cancellation. -/
def coneComparisonMinus : (oldConeMinus P p q).Homotopy
    ((polynomialMovementMinus P p q).trans (newConeMinus P p q)) :=
  (coneSquareTypedMinus P p q).coneBoundary

/-- Endpoint retyping leaves the entire cone comparison unchanged. -/
theorem coneComparisonMinus_apply (r s : I) :
    coneComparisonMinus P p q (r, s) = coneBoundaryMinus P p q (r, s) :=
  (coneSquareMinus P p q).rebaseMovement_coneBoundary_apply
    (polynomialMovementMinus P p q) (polynomialMinus_seam P p q) r s

/-- The literal old null word has the original two nested path subdivisions. -/
abbrev oldNullMinus := (oldPositiveMinus P p q).trans
  ((positiveMovementMinus P p q).trans (oldConeMinus P p q))

/-- The literal new null word retains the separate minus tip. -/
abbrev newNullMinus := (newPositiveMinus P p q).trans (newConeMinus P p q)

/-- Original straight-positive word applied to this actual full rectangle. -/
def straightPositiveMinus :
    (((oldPositiveMinus P p q).trans (positiveMovementMinus P p q)).trans
      (polynomialMovementMinus P p q)).Homotopy
        ((laurentMovementMinus P p q).trans (newPositiveMinus P p q)) :=
  Path.Homotopy.straightPositiveWord (oldPositiveMinus P p q)
    (positiveMovementMinus P p q) (polynomialMovementMinus P p q)
    (laurentMovementMinus P p q) (newPositiveMinus P p q) (rectangleMinus P p q)

/-- The minus paired-null constituent uses the literal original five-stage recipe. -/
def pastedNullMinus : (oldNullMinus P p q).Homotopy
    ((laurentMovementMinus P p q).trans (newNullMinus P p q)) :=
  Path.Homotopy.pastedPositiveNullWord (oldPositiveMinus P p q)
    (positiveMovementMinus P p q) (polynomialMovementMinus P p q)
    (laurentMovementMinus P p q) (newPositiveMinus P p q)
    (oldConeMinus P p q) (newConeMinus P p q) (rectangleMinus P p q)
    (coneComparisonMinus P p q)

/-- The plus old cone has the rectangle rail's exact source type. -/
abbrev oldConePlus := (coneSquarePlus P p q).rebaseOld
  (polynomialMovementPlus P p q) (polynomialPlus_seam P p q)

/-- The plus new cone retains its own original tip. -/
abbrev newConePlus := (coneSquarePlus P p q).rebaseNew
  (polynomialMovementPlus P p q) (polynomialPlus_seam P p q)

/-- The complete original square, with its lower rail named by the actual rectangle. -/
abbrev coneSquareTypedPlus := (coneSquarePlus P p q).rebaseMovement
  (polynomialMovementPlus P p q) (polynomialPlus_seam P p q)

/-- The actual collapse followed by the unchanged terminal-pause cancellation. -/
def coneComparisonPlus : (oldConePlus P p q).Homotopy
    ((polynomialMovementPlus P p q).trans (newConePlus P p q)) :=
  (coneSquareTypedPlus P p q).coneBoundary

/-- Endpoint retyping leaves the entire cone comparison unchanged. -/
theorem coneComparisonPlus_apply (r s : I) :
    coneComparisonPlus P p q (r, s) = coneBoundaryPlus P p q (r, s) :=
  (coneSquarePlus P p q).rebaseMovement_coneBoundary_apply
    (polynomialMovementPlus P p q) (polynomialPlus_seam P p q) r s

/-- The literal old null word has the original two nested path subdivisions. -/
abbrev oldNullPlus := (oldPositivePlus P p q).trans
  ((positiveMovementPlus P p q).trans (oldConePlus P p q))

/-- The literal new null word retains the separate plus tip. -/
abbrev newNullPlus := (newPositivePlus P p q).trans (newConePlus P p q)

/-- Original straight-positive word applied to this actual full rectangle. -/
def straightPositivePlus :
    (((oldPositivePlus P p q).trans (positiveMovementPlus P p q)).trans
      (polynomialMovementPlus P p q)).Homotopy
        ((laurentMovementPlus P p q).trans (newPositivePlus P p q)) :=
  Path.Homotopy.straightPositiveWord (oldPositivePlus P p q)
    (positiveMovementPlus P p q) (polynomialMovementPlus P p q)
    (laurentMovementPlus P p q) (newPositivePlus P p q) (rectanglePlus P p q)

/-- The plus paired-null constituent uses the literal original five-stage recipe. -/
def pastedNullPlus : (oldNullPlus P p q).Homotopy
    ((laurentMovementPlus P p q).trans (newNullPlus P p q)) :=
  Path.Homotopy.pastedPositiveNullWord (oldPositivePlus P p q)
    (positiveMovementPlus P p q) (polynomialMovementPlus P p q)
    (laurentMovementPlus P p q) (newPositivePlus P p q)
    (oldConePlus P p q) (newConePlus P p q) (rectanglePlus P p q)
    (coneComparisonPlus P p q)

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0PairedNull
