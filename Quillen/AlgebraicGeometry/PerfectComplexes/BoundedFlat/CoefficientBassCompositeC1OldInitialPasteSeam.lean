/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeC1OldSourceRails

/-! Original chart/cylinder half clocks for the composite-arrow C1 entrance. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassCompositeC1OldInitialPasteSeam
open CoefficientBassCompositeJ0Rectangles CoefficientBassCompositeJ0PairedNull
open CoefficientBassCompositeC1OldSourceRails
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The ordinary initial paste has exactly the old movement followed by its old cone path. -/
theorem initial_minus (s : I) :
    CoefficientBassPositiveC1InitialMovingNull.parameter P
      p q (0, s) =
      ((positiveMovementMinus P p q).trans (oldConeMinus P p q)) s := by
  change ((CoefficientBassPositiveC1InitialMovingNull.firstSwap P
    p q).trans
      (CoefficientBassPositiveC1InitialMovingNull.lastSwap P
        p q)) (s, 0) = _
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs
  · exact chart_minus P p q _
  · exact minus_cylinder P p q _

/-- The shifted initial paste has the same literal halves and retains its distinct plus tip. -/
theorem initial_plus (s : I) :
    CoefficientBassPositiveC1ShiftedInitialMovingNull.parameter P
      p q (0, s) =
      ((positiveMovementPlus P p q).trans (oldConePlus P p q)) s := by
  change ((CoefficientBassPositiveC1ShiftedInitialMovingNull.firstSwap P
    p q).trans
      (CoefficientBassPositiveC1ShiftedInitialMovingNull.lastSwap P
        p q)) (s, 0) = _
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs
  · exact chart_plus P p q _
  · exact plus_cylinder P p q _

end Quillen.PerfectComplexes.CoefficientBassCompositeC1OldInitialPasteSeam
