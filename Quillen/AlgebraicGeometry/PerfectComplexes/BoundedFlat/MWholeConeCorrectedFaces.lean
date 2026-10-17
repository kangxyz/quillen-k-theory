/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeCorrectedSquare

/-! Whole scalar faces of the original corrected M cone-composition cube. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

theorem corrected_zero (s t : I) :
    corrected P p q (0, (s, t)) = lowerPath P p q s t :=
  congrArg (fun f ↦ f t) ((correctedSquare P p q).at_zero s)

theorem corrected_one (s t : I) :
    corrected P p q (1, (s, t)) = correctedUpper P p q s t :=
  congrArg (fun f ↦ f t) ((correctedSquare P p q).at_one s)

theorem corrected_left (r t : I) :
    corrected P p q (r, (0, t)) = cube P p q (r, (0, t)) :=
  congrArg (fun f ↦ f t) ((correctedSquare P p q).left r)

theorem corrected_right (r t : I) :
    corrected P p q (r, (1, t)) = endTip P p q t :=
  congrArg (fun f ↦ f t) ((correctedSquare P p q).right r)

end Quillen.PerfectComplexes.BassMWholeConeCarrier
