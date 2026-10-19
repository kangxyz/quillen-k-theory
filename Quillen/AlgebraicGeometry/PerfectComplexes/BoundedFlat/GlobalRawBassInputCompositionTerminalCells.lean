/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionTerminalProducts
public import Quillen.Topology.Prespectrum.NativeH1CellOps

/-!
# Every original cell of the terminal global input-composition face

The first attached input surface and the three actual span-precomposition pieces recover the
four original parameter regions of H1. These native equalities include all boundary values;
full carrier joins and the resulting whole H1 surface remain separate obligations.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.NativePathCells
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTerminalCells
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The actual second comparison half keeps the entire original span map on its input. -/
theorem second_half (n : ℕ) (s : unitInterval) (x : (span Z).space n) :
    (InputCompositionCharts.compositeComparison f g).level n (upper s, x) =
      (inputComparisonHomotopy f).level n (s, (spanMap g).map n x) :=
  coneSquarePasted_upper_cell (comparison Z) (comparison Y) (comparison X)
    (spanMap g) (boundedFlatPerfectPrespectrumMap (laurent.map g))
    (spanMap f) (boundedFlatPerfectPrespectrumMap (laurent.map f))
    (inputComparisonHomotopy g) (inputComparisonHomotopy f) n s x

/-- The original first span half retains every polynomial-square point. -/
theorem span_lower (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    (spanMap g).map n
      (HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app Z))
        (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (lower t, x)) =
      (HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (projection.app Y))
        (boundedFlatPerfectPrespectrumMap (projection.app Y))).map n
          ((polynomialSquareHomotopy g).level n (t, x)) :=
  HomotopyPushout.mapOfHomotopies_lower_cell _ _ _ _ _ _ _ _ _ n t x

/-- The middle quarter retains the unchanged cylinder with its actual base-arrow input. -/
theorem span_middle (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    (spanMap g).map n
      (HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app Z))
        (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (upper (lower t), x)) =
      HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app Y))
        (boundedFlatPerfectPrespectrumMap (projection.app Y)) n
          (t, (boundedFlatPerfectPrespectrumMap g).map n x) :=
  HomotopyPushout.mapOfHomotopies_middle_cell _ _ _ _ _ _ _ _ _ n t x

/-- The final quarter retains the original inverse square with only its height reversed. -/
theorem span_upper (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    (spanMap g).map n
      (HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app Z))
        (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (upper (upper t), x)) =
      (HomotopyPushout.inr (boundedFlatPerfectPrespectrumMap (projection.app Y))
        (boundedFlatPerfectPrespectrumMap (projection.app Y))).map n
          ((polynomialSquareHomotopy g).level n (unitInterval.symm t, x)) :=
  HomotopyPushout.mapOfHomotopies_upper_cell _ _ _ _ _ _ _ _ _ n t x

/-- The actual positive product is H1 on its entire original half-by-half region. -/
theorem plus_cell (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (InputCompositionTerminalProducts.face f g plus plus_projection) n ((s, t), x) =
      (InputCompositionCharts.compositeComparison f g).level n
        (upper s, HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (lower t, x)) := by
  rw [InputCompositionTerminalProducts.face_native, second_half, span_lower]
  exact (inputComparisonHomotopy_inl f n s _).symm

/-- The whole preattached input surface is H1 on its unchanged middle quarter. -/
theorem middle_cell (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (InputCompositionTerminalAttach.preFace f g) n ((s, t), x) =
      (InputCompositionCharts.compositeComparison f g).level n
        (upper s, HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (upper (lower t), x)) := by
  rw [InputCompositionTerminalAttach.pre_native, second_half, span_middle]

/-- The whole inverse product is H1 on the original last quarter, including its reversal. -/
theorem minus_cell (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (InputCompositionTerminalProducts.face f g minus minus_projection) n
        ((s, unitInterval.symm t), x) =
      (InputCompositionCharts.compositeComparison f g).level n
        (upper s, HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (upper (upper t), x)) := by
  rw [InputCompositionTerminalProducts.face_native, second_half, span_upper]
  exact (inputComparisonHomotopy_inr f n s _).symm

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTerminalCells
