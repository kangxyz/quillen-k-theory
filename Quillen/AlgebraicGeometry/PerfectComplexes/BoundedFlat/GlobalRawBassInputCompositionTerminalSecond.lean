/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionTerminalSeams
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionTerminalCells
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNervePointwiseFamily

/-!
# The whole original second half of terminal input composition

Both proved full carrier joins paste the positive product, original input surface and reversed
inverse product. The exact original half/quarter/quarter overlap allocation recovers every
native point of the second comparison half. No first/second-half seam is supplied here.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.NativePathCells Quillen.ScalarRectangle
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTerminalSecond
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Only the inverse product's original overlap coordinate is reversed. -/
def minusFace : C(unitInterval × unitInterval, InputCompositionCarrierCharts.Carrier f g) :=
  ⟨fun z ↦ InputCompositionTerminalProducts.face f g minus minus_projection
    (z.1, unitInterval.symm z.2), by fun_prop⟩

/-- The whole middle-to-inverse edge agrees in the full reference carrier. -/
theorem middle_minus (s : unitInterval) :
    InputCompositionTerminalAttach.preFace f g (s, 1) = minusFace f g (s, 0) := by
  change _ = InputCompositionTerminalProducts.face f g minus minus_projection
    (s, unitInterval.symm 0)
  rw [unitInterval.symm_zero]
  exact (InputCompositionTerminalSeams.minus_middle f g s).symm

/-- The original middle and reversed inverse pieces are joined at their full common edge. -/
def tailFace : C(unitInterval × unitInterval, InputCompositionCarrierCharts.Carrier f g) :=
  concatSecond (InputCompositionTerminalAttach.preFace f g) (minusFace f g) (middle_minus f g)

/-- The whole positive-to-tail edge uses the original proved positive middle seam. -/
theorem plus_tail (s : unitInterval) :
    InputCompositionTerminalProducts.face f g plus plus_projection (s, 1) =
      tailFace f g (s, 0) := by
  rw [tailFace, concatSecond_zero]
  exact InputCompositionTerminalSeams.plus_middle f g s

/-- The entire original second comparison half, preserving its three actual overlap pieces. -/
def face : C(unitInterval × unitInterval, InputCompositionCarrierCharts.Carrier f g) :=
  concatSecond (InputCompositionTerminalProducts.face f g plus plus_projection)
    (tailFace f g) (plus_tail f g)

/-- The first overlap half is the entire original positive product. -/
theorem face_plus (s t : unitInterval) :
    face f g (s, lower t) =
      InputCompositionTerminalProducts.face f g plus plus_projection (s, t) :=
  concatSecond_lower _ _ _ s t

/-- The middle quarter is the whole original preattached input surface. -/
theorem face_middle (s t : unitInterval) :
    face f g (s, upper (lower t)) = InputCompositionTerminalAttach.preFace f g (s, t) := by
  rw [face, concatSecond_upper, tailFace, concatSecond_lower]

/-- The last quarter retains the original inverse product and only its prescribed reversal. -/
theorem face_minus (s t : unitInterval) :
    face f g (s, upper (upper t)) =
      InputCompositionTerminalProducts.face f g minus minus_projection
        (s, unitInterval.symm t) := by
  rw [face, concatSecond_upper, tailFace, concatSecond_upper]
  rfl

/-- Every original second-half native point is recovered at all levels and overlap heights. -/
theorem face_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (face f g) n ((s, t), x) =
      (InputCompositionCharts.compositeComparison f g).level n
        (upper s, HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (t, x)) := by
  refine (CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
    (InputCompositionCarrierCharts.source f g) (face f g) n (s, t) x).symm.trans ?_
  rcases three_cover t with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩
  · rw [face_plus]
    exact (CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
      (InputCompositionCarrierCharts.source f g)
      (InputCompositionTerminalProducts.face f g plus plus_projection) n (s, q) x).trans
        (InputCompositionTerminalCells.plus_cell f g n s q x)
  · rw [face_middle]
    exact (CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
      (InputCompositionCarrierCharts.source f g)
      (InputCompositionTerminalAttach.preFace f g) n (s, q) x).trans
        (InputCompositionTerminalCells.middle_cell f g n s q x)
  · rw [face_minus]
    exact (CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
      (InputCompositionCarrierCharts.source f g)
      (InputCompositionTerminalProducts.face f g minus minus_projection)
      n (s, unitInterval.symm q) x).trans
        (InputCompositionTerminalCells.minus_cell f g n s q x)

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTerminalSecond
