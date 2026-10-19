/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionTransformations
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionSpan
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputMap
public import Quillen.Topology.Prespectrum.ConeSquareMapComposition

/-!
# Actual chart faces of global raw input composition

The whole positive and inverse polynomial-chart faces use the unchanged original input
comparison, Laurent composition and span composition. The terminal chart pauses of the
span producer are retained exactly. No whole comparison square or cylinder cube is assumed
or asserted here.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionCharts
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The original Laurent composition track with its actual functor composition transport. -/
def laurentComposition := InputCompositionTransformations.composition f g laurent

/-- The two successive original input comparisons in the exact cone-composition interface. -/
def compositeComparison :=
  coneSquarePastedHomotopy (comparison Z) (comparison Y) (comparison X)
    (spanMap g) (boundedFlatPerfectPrespectrumMap (laurent.map g))
    (spanMap f) (boundedFlatPerfectPrespectrumMap (laurent.map f))
    (inputComparisonHomotopy g) (inputComparisonHomotopy f)

/-- The unchanged Laurent boundary of the desired comparison square. -/
def laurentTrack := Homotopy.precomp (comparison Z) (laurentComposition f g)

/-- The actual whole span-composition boundary, with its prescribed terminal chart pauses. -/
def spanTrack := (InputCompositionSpan.homotopy f g).postcomp (comparison X)

/-- The exact chart restriction of the intended original comparison-composition square. -/
abbrev ChartSquare
    (i : originalPrespectrum (boundedFlatPerfectWaldhausen (polynomial.obj Z)) ⟶ span Z) :=
  (Homotopy.precomp i (inputComparisonHomotopy (f ≫ g))).Square
    (Homotopy.precomp i (compositeComparison f g))
    (Homotopy.precomp i (laurentTrack f g))
    (Homotopy.precomp i (spanTrack f g))

/-- The complete native plus chart is constructed from the original transposed rectangle.
Its span boundary includes exactly the terminal pause present in the fixed span homotopy. -/
def plusChart :
    ChartSquare f g
      (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (projection.app Z))
        (boundedFlatPerfectPrespectrumMap (projection.app Z))) := by
  refine (InputCompositionTransformations.movingSquare plus f g).pauseRight
    |>.ofBoundaryLevels _ _ _ _ ?_ ?_ ?_ ?_
  · intro n
    rfl
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    change (((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n))
      (r, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (projection.app Z))
        (boundedFlatPerfectPrespectrumMap (projection.app Z))).map n x)) =
      ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)
    rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split <;> rfl
  · intro n
    rfl
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    change (comparison X).map n
      ((InputCompositionSpan.homotopy f g).level n
        (r, (HomotopyPushout.inl
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z))).map n x)) = _
    rw [InputCompositionSpan.homotopy_inl]
    change (comparison X).map n
      (((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)) =
      ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)
    rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split <;> rfl

/-- The separate native minus chart retains the inverse-coordinate transformation verbatim. -/
def minusChart :
    ChartSquare f g
      (HomotopyPushout.inr
        (boundedFlatPerfectPrespectrumMap (projection.app Z))
        (boundedFlatPerfectPrespectrumMap (projection.app Z))) := by
  refine (InputCompositionTransformations.movingSquare minus f g).pauseRight
    |>.ofBoundaryLevels _ _ _ _ ?_ ?_ ?_ ?_
  · intro n
    rfl
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    change (((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n))
      (r, (HomotopyPushout.inr
        (boundedFlatPerfectPrespectrumMap (projection.app Z))
        (boundedFlatPerfectPrespectrumMap (projection.app Z))).map n x)) =
      ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)
    rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split <;> rfl
  · intro n
    rfl
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    change (comparison X).map n
      ((InputCompositionSpan.homotopy f g).level n
        (r, (HomotopyPushout.inr
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z))).map n x)) = _
    rw [InputCompositionSpan.homotopy_inr]
    change (comparison X).map n
      (((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)) =
      ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)
    rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split <;> rfl

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionCharts
