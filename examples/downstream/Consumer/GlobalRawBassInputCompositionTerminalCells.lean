/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionTerminalCells

/-! Exact original terminal comparison cells, including all region boundaries. -/
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
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
namespace Consumer.GlobalRawBassInputCompositionTerminalCells
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The actual positive product is H1 on its entire original half-by-half region. -/
theorem plus_cell (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (InputCompositionTerminalProducts.face f g plus plus_projection) n ((s, t), x) =
      (InputCompositionCharts.compositeComparison f g).level n
        (upper s, HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (lower t, x)) :=
  InputCompositionTerminalCells.plus_cell f g n s t x

/-- The whole preattached input surface is H1 on its unchanged middle quarter. -/
theorem middle_cell (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (InputCompositionTerminalAttach.preFace f g) n ((s, t), x) =
      (InputCompositionCharts.compositeComparison f g).level n
        (upper s, HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (upper (lower t), x)) :=
  InputCompositionTerminalCells.middle_cell f g n s t x

/-- The whole inverse product is H1 on the original last quarter, including its reversal. -/
theorem minus_cell (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (InputCompositionTerminalProducts.face f g minus minus_projection) n
        ((s, unitInterval.symm t), x) =
      (InputCompositionCharts.compositeComparison f g).level n
        (upper s, HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (upper (upper t), x)) :=
  InputCompositionTerminalCells.minus_cell f g n s t x

end Consumer.GlobalRawBassInputCompositionTerminalCells
