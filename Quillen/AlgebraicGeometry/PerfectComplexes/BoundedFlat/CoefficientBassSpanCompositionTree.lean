/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSpanCompositionReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PolynomialMovingFamily
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeMovingSquare

/-!
# The original coefficient span vertex square in the four-edge tree

The two polynomial charts retain the reanchored eighteen-node square. Their common seam is
its exact source-composition row, and the middle piece retains the independent overlap time.
Evaluation recovers the original native span square, with its original boundary casts.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSpanCompositionReference
open CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
local notation "E" => coefficientReference P p q
local notation "J" => polynomialMap P (c := c)

/-- The original polynomial square has the literal simplicial attachment as its whole right side. -/
theorem polynomialSquare_attachment (r : I) :
    polynomialSquare P p q (r, 1) =
      SSet.toTop.map (FourEdgeTree.attachment E J) (coefficientPath P p q r) :=
  polynomialSquare_right P p q r

/-- The same square evaluates to the maintained polynomial owner, without changing its casts. -/
theorem polynomialSquare_original_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    pointwisePrespectrumFamily (polynomialReference P p q) n
        (polynomialSquare P p q (r, s)) x =
      (boundedFlatCoefficientPolynomialCompositionSquare P p q).level n (r, (s, x)) := by
  change pointwisePrespectrumFamily _ n (CommonReferenceNerve.parameter _ (squareNodes P p q)
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, s))) x = _
  rw [pointwisePrespectrumFamily_parameter, square_parameter_native,
    ← BassMComponents.polynomial_simplex_original]
  exact BassMComponents.polynomial_moving_native P p q n r s x

/-- The actual three-piece span square keeps both polynomial charts and the whole overlap. -/
def treeSquare : C(I × I, FourEdgeTree.space E J) :=
  FourEdgeTree.movingSquare E J (polynomialSquare P p q) (coefficientPath P p q)
    (polynomialSquare_attachment P p q)

/-- The first original half is the complete polynomial square in the positive summand. -/
theorem treeSquare_lower (r t : I) :
    treeSquare P p q (r, lower t) =
      SSet.toTop.map (FourEdgeTree.plusVertex E J) (polynomialSquare P p q (r, t)) :=
  FourEdgeTree.movingSquare_lower E J _ _ _ r t

/-- The middle original quarter has two independent, unchanged coordinates. -/
theorem treeSquare_middle (r t : I) :
    treeSquare P p q (r, upper (lower t)) =
      FourEdgeTree.overlap E J (coefficientPath P p q r, t) :=
  FourEdgeTree.movingSquare_middle E J _ _ _ r t

/-- The final original quarter retains the reversed polynomial path in the inverse summand. -/
theorem treeSquare_upper (r t : I) :
    treeSquare P p q (r, upper (upper t)) =
      SSet.toTop.map (FourEdgeTree.minusVertex E J)
        (polynomialSquare P p q (r, unitInterval.symm t)) :=
  FourEdgeTree.movingSquare_upper E J _ _ _ r t

/-- The positive boundary retains the entire polynomial target-composition path. -/
theorem treeSquare_left (r : I) :
    treeSquare P p q (r, 0) = SSet.toTop.map (FourEdgeTree.plusVertex E J)
      (mapParameter (targetAttachmentNode P p q)
        (coefficientPath P ((polynomialUnderFunctor R).map p)
          ((polynomialUnderFunctor R).map q) r)) := by
  rw [treeSquare, FourEdgeTree.movingSquare_left, polynomialSquare_left]

/-- The inverse boundary retains the same target-composition path in its separate chart. -/
theorem treeSquare_right (r : I) :
    treeSquare P p q (r, 1) = SSet.toTop.map (FourEdgeTree.minusVertex E J)
      (mapParameter (targetAttachmentNode P p q)
        (coefficientPath P ((polynomialUnderFunctor R).map p)
          ((polynomialUnderFunctor R).map q) r)) := by
  rw [treeSquare, FourEdgeTree.movingSquare_right, polynomialSquare_left]

/-- Every level, including zero, recovers the original native span composition square. -/
theorem treeSquare_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdgeTree.nativeEval E J n (treeSquare P p q (r, s)) x =
      (boundedFlatCoefficientPolynomialSpanCompositionSquare P p q).level n (r, (s, x)) := by
  let S := (boundedFlatCoefficientPolynomialCompositionSquare P p q).ofBoundaryLevels
    (boundedFlatCoefficientPolynomialSquareHomotopy P (p ≫ q))
    (boundedFlatCoefficientPolynomialCompositeDescSquare P p q)
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatCoefficientPolynomialCompositionHomotopy P p q))
    (boundedFlatCoefficientPolynomialSourceCompositionTrack P p q)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  exact FourEdgeTree.movingSquare_native E J
    (polynomialSquare P p q) (coefficientPath P p q) (polynomialSquare_attachment P p q)
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientPolynomialSquareHomotopy P (p ≫ q))
    (boundedFlatCoefficientPolynomialCompositeDescSquare P p q)
    (boundedFlatCoefficientCompositionHomotopy P p q)
    (boundedFlatCoefficientPolynomialCompositionHomotopy P p q) S n x
    (fun r t ↦ polynomialSquare_original_native P p q n r t x)
    (fun r ↦ coefficientPath_native P p q n r x) r s

/-- On each whole source cylinder, this is the original vertex-composition homotopy. -/
theorem treeSquare_vertex_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdgeTree.nativeEval E J n (treeSquare P p q (r, s)) x =
      (boundedFlatCoefficientPolynomialSpanVertexCompositionHomotopy P p q).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (s, x)) :=
  treeSquare_native P p q n r s x

end Quillen.PerfectComplexes.CoefficientBassSpanCompositionReference
