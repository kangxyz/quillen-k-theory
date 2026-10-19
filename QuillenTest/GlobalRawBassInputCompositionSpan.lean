/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionSpan

/-! Whole-boundary regressions for actual global polynomial-span composition. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
universe u
namespace QuillenTest.GlobalRawBassInputCompositionSpan
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The pilot uses the actual direct span map and actual composite, not replaced maps. -/
def originalSpanComposition : Homotopy (spanMap (f ≫ g)) (spanMap g ≫ spanMap f) :=
  InputCompositionSpan.homotopy f g

/-- The geometric lower side is precisely the original polynomial composition track. -/
theorem polynomial_bottom (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    (InputCompositionPolynomial.square f g).level n (r, (0, x)) =
      (InputCompositionPolynomial.targetTrack f g).level n (r, x) :=
  (InputCompositionPolynomial.square f g).left n r x

/-- The entire first-half cylinder recovers the selected moving square. -/
theorem whole_cylinder_first (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    (originalSpanComposition f g).level n
      (Quillen.NativePathCells.lower r,
        HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (s, x)) =
      (InputCompositionSpan.movingSquare f g).level n (r, (s, x)) :=
  InputCompositionSpan.homotopy_cylinder_lower f g n r s x

/-- The second half keeps the actual five-piece cylinder reassociation in reverse. -/
theorem whole_cylinder_second (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    (originalSpanComposition f g).level n
      (Quillen.NativePathCells.upper r,
        HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (s, x)) =
      (HomotopyPushout.identicalLegCompositionPasting
        (boundedFlatPerfectPrespectrumMap (projection.app Z))
        (boundedFlatPerfectPrespectrumMap (projection.app Y))
        (boundedFlatPerfectPrespectrumMap (projection.app X))
        (boundedFlatPerfectPrespectrumMap g)
        (boundedFlatPerfectPrespectrumMap (polynomial.map g))
        (boundedFlatPerfectPrespectrumMap f)
        (boundedFlatPerfectPrespectrumMap (polynomial.map f))
        (polynomialSquareHomotopy g) (polynomialSquareHomotopy f)).level n
          (unitInterval.symm r, (s, x)) :=
  InputCompositionSpan.homotopy_cylinder_upper f g n r s x

/-- The chosen second-half chart pause is retained on the whole positive polynomial leaf. -/
theorem polynomial_chart_pause (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (polynomial.obj Z))).space n) :
    (InputCompositionSpan.homotopy f g).level n
      (Quillen.NativePathCells.upper r,
        (HomotopyPushout.inl
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z))).map n x) =
      (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (projection.app X))
        (boundedFlatPerfectPrespectrumMap (projection.app X))).map n
          ((boundedFlatPerfectPrespectrumMap (polynomial.map f)).map n
            ((boundedFlatPerfectPrespectrumMap (polynomial.map g)).map n x)) := by
  rw [InputCompositionSpan.homotopy_inl]
  exact Homotopy.trans_upper_cell _ _ n r x

/-- Comparison and prespectrum structure parameters remain independent on every span point. -/
theorem independent_structure (n : ℕ) (r t : unitInterval) (x : (span Z).space n) :
    (originalSpanComposition f g).level (n + 1) (r, (span Z).structureMap n x t) =
      (span X).structureMap n ((originalSpanComposition f g).level n (r, x)) t :=
  InputCompositionSpan.homotopy_structure f g n r t x

/-- The positive chart pair has the original Laurent source map literally. -/
def positivePair (X : Scheme.{u}) :
    Homotopy (spanMap (laurentProjection.app X))
      (spanMap (projection.app X) ≫ spanMap (plus.app X)) :=
  InputCompositionSpan.positiveProjection X

/-- Every initial point of the positive pilot is the actual Laurent input span map. -/
theorem positive_source (X : Scheme.{u}) (n : ℕ) (x : (span X).space n) :
    (positivePair X).level n (0, x) = (spanMap (laurentProjection.app X)).map n x :=
  (positivePair X).at_zero n x

/-- Every final point of the positive pilot is the unchanged two-map composite. -/
theorem positive_target (X : Scheme.{u}) (n : ℕ) (x : (span X).space n) :
    (positivePair X).level n (1, x) =
      (spanMap (plus.app X)).map n ((spanMap (projection.app X)).map n x) :=
  (positivePair X).at_one n x

/-- The inverse-coordinate pair uses its own actual minus map in the same whole producer. -/
def inversePair (X : Scheme.{u}) :
    Homotopy (spanMap (laurentProjection.app X))
      (spanMap (projection.app X) ≫ spanMap (minus.app X)) :=
  (InputCompositionSpan.homotopy (minus.app X) (projection.app X)).cast
    (congrArg spanMap (minus_projection X)) rfl

end QuillenTest.GlobalRawBassInputCompositionSpan
