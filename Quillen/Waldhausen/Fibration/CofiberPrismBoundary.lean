/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Homotopy.SquareBoundaryPaths
public import Quillen.Waldhausen.GrothendieckComparison.CofiberPrismComposition
public import Quillen.Waldhausen.GrothendieckComparison.WeakObjectSquareTrack
public import Quillen.Waldhausen.Fibration.IdentityCofiberComponent

/-!
# The two prescribed boundary routes of the original cofiber prism

The actual square of based loops gives an explicit relative comparison of prefix-then-cofiber
and identity-suffix-then-inclusion. All three coordinates survive the construction. These are
the forward prism routes; the canonical fiber supplies the reversed prefix in the later
boundary calculation, whose sign is not asserted by this module.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits unitInterval
open Quillen.Waldhausen.QuotientRows
open scoped Topology
universe u v
namespace Quillen.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : W.cof i) (hwi : W.weq i)
  (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q))

/-- The original loop-space square compares its two entire prescribed boundary routes. -/
def cofiberPrismBoundaryHomotopy :
    ((((Path.refl (0 : unitInterval)).prod Path.id).map
        (W.cofiberPrismCompositionLoops i q hi hwi hQ).continuous).trans
      ((Path.id.prod (Path.refl (1 : unitInterval))).map
        (W.cofiberPrismCompositionLoops i q hi hwi hQ).continuous)).Homotopy
      (((Path.id.prod (Path.refl (0 : unitInterval))).map
        (W.cofiberPrismCompositionLoops i q hi hwi hQ).continuous).trans
          (((Path.refl (1 : unitInterval)).prod Path.id).map
            (W.cofiberPrismCompositionLoops i q hi hwi hQ).continuous)) :=
  squareBoundaryPathHomotopy (W.cofiberPrismCompositionLoops i q hi hwi hQ)

/-- Comparison, boundary-path and original object-loop times remain independent. -/
theorem cofiberPrismBoundaryHomotopy_apply (a s t : unitInterval) :
    W.cofiberPrismBoundaryHomotopy i q hi hwi hQ (a, s) t =
      W.cofiberPrismCompositionCube i q hi hwi hQ
        ((unitSquarePathHomotopy
          (((Path.refl (0 : unitInterval)).prod Path.id).trans
            (Path.id.prod (Path.refl (1 : unitInterval))))
          ((Path.id.prod (Path.refl (0 : unitInterval))).trans
            ((Path.refl (1 : unitInterval)).prod Path.id)) (a, s)).1,
          (unitSquarePathHomotopy
            (((Path.refl (0 : unitInterval)).prod Path.id).trans
              (Path.id.prod (Path.refl (1 : unitInterval))))
            ((Path.id.prod (Path.refl (0 : unitInterval))).trans
              ((Path.refl (1 : unitInterval)).prod Path.id)) (a, s)).2, t) := rfl

/-- The first route is the original forward quotient prefix followed by its cofiber triangle. -/
theorem cofiberPrismBoundaryHomotopy_zero (s t : unitInterval) :
    W.cofiberPrismBoundaryHomotopy i q hi hwi hQ (0, s) t =
      if h : (s : ℝ) ≤ 1 / 2 then
        W.cofiberPrismCompositionCube i q hi hwi hQ
          (0, ⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, h⟩⟩, t)
      else
        W.cofiberObjectLoopTrack i q hi hQ
          (⟨2 * s - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, s.2.2⟩⟩, t) := by
  rw [ContinuousMap.HomotopyWith.apply_zero]
  change (((((Path.refl (0 : unitInterval)).prod Path.id).map
    (W.cofiberPrismCompositionLoops i q hi hwi hQ).continuous).trans
      ((Path.id.prod (Path.refl (1 : unitInterval))).map
        (W.cofiberPrismCompositionLoops i q hi hwi hQ).continuous)) s) t = _
  rw [Path.trans_apply]
  split_ifs with h
  · rfl
  · exact W.cofiberPrismCompositionCube_nerve_one i q hi hwi hQ _ t

/-- The second route is the actual identity-triangle suffix followed by the inclusion square. -/
theorem cofiberPrismBoundaryHomotopy_one (s t : unitInterval) :
    W.cofiberPrismBoundaryHomotopy i q hi hwi hQ (1, s) t =
      if h : (s : ℝ) ≤ 1 / 2 then
        W.identityCofiberSuffixPath A
          ⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, h⟩⟩ t
      else
        W.weakObjectSquareTrack i hwi
          (⟨2 * s - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, s.2.2⟩⟩, t) := by
  rw [ContinuousMap.HomotopyWith.apply_one]
  change (Path.trans
    ((Path.id.prod (Path.refl (0 : unitInterval))).map
      (W.cofiberPrismCompositionLoops i q hi hwi hQ).continuous)
    (((Path.refl (1 : unitInterval)).prod Path.id).map
      (W.cofiberPrismCompositionLoops i q hi hwi hQ).continuous) s) t = _
  rw [Path.trans_apply]
  split_ifs with h
  · exact W.cofiberPrismCompositionCube_nerve_zero i q hi hwi hQ _ t
  · exact W.cofiberPrismCompositionCube_comparison_one i q hi hwi hQ _ t

end Quillen.Waldhausen.Structure
