/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Fibration.CofiberPrismFiber

/-! # Actual cofiber-prism faces and reversed quotient-fiber consumers -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Convexity unitInterval
open Quillen.Waldhausen Quillen.Waldhausen.QuotientRows Quillen.Waldhausen.Fibration
open scoped Simplicial Topology
universe u v
namespace Quillen.Tests.CofiberPrismComposition
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : W.cof i) (hwi : W.weq i)
  (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q))

/-- The initial nerve face retains the actual identity-cofiber composition track. -/
theorem original_identity_track (r t : unitInterval) :
    W.cofiberPrismCompositionCube i q hi hwi hQ (r, 0, t) =
      W.cofiberObjectLoopTrack (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
        (cofiberTwo_identity_square W) (r, t) :=
  W.cofiberPrismCompositionCube_nerve_zero i q hi hwi hQ r t

/-- The terminal nerve face retains the original displayed quotient composition track. -/
theorem original_quotient_track (r t : unitInterval) :
    W.cofiberPrismCompositionCube i q hi hwi hQ (r, 1, t) =
      W.cofiberObjectLoopTrack i q hi hQ (r, t) :=
  W.cofiberPrismCompositionCube_nerve_one i q hi hwi hQ r t

/-- The original comparison, nerve and loop coordinates survive the actual currying. -/
theorem original_three_coordinates (r s t : unitInterval) :
    W.cofiberPrismCompositionLoops i q hi hwi hQ (r, s) t =
      W.cofiberPrismCompositionCube i q hi hwi hQ (r, s, t) :=
  W.cofiberPrismCompositionLoops_apply i q hi hwi hQ r s t

omit [HasZeroMorphisms C] in
/-- The entire identity weak square is the literal original object edge at every nerve time. -/
theorem original_identity_square (s t : unitInterval) :
    bisimplexRealization W (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s) =
      W.kZeroObjectLoop A t :=
  W.weakObjectIdentitySquare_realization A s t

/-- The whole original weak-cofibration square occurs on the comparison-one face. -/
theorem original_weak_cofibration_square (s t : unitInterval) :
    W.cofiberPrismCompositionCube i q hi hwi hQ (1, s, t) =
      bisimplexRealization W (W.weakObjectSimplex i hwi).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex i hwi).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s) :=
  W.cofiberPrismCompositionCube_comparison_one i q hi hwi hQ s t

section Fiber
variable {V : Structure C} (N : NestedWeakEquivalences V)
  (hi : N.coarse.cof i) (hwi : N.coarse.weq i)
  (hQ : IsPushout i (0 : A ⟶ N.coarse.zero) q (0 : N.coarse.zero ⟶ Q))

/-- The actual quotient square is the unchanged reversed canonical-fiber coordinate. -/
theorem original_quotient_fiber (t s : unitInterval) :
    N.coarse.cofiberPrismRealization i q hi hwi hQ
        ((StdSimplex.homeomorphI.symm t).map (SimplexCategory.δ 0), unitInterval.symm s) =
      (canonicalFiberObjectLoop N (cofiberPrismAcyclicQuotient N i q hi hwi hQ) t).val.2 s :=
  cofiberPrismRealization_quotient_fiber N i q hi hwi hQ t s

/-- Original source-prefix translation keeps its actual half-interval and full fiber coordinate. -/
theorem original_translated_fiber (t s : unitInterval) :
    N.coarse.cofiberPrismCompositionCube i q hi hwi hQ (0, unitInterval.symm s, t) =
      if h : (t : ℝ) ≤ 1 / 2 then
        N.coarse.kZeroObjectLoop A
          ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
      else
        (canonicalFiberObjectLoop N (cofiberPrismAcyclicQuotient N i q hi hwi hQ)
          ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩).val.2 s :=
  cofiberPrismCompositionCube_zero_fiber N i q hi hwi hQ t s
end Fiber

end Quillen.Tests.CofiberPrismComposition
