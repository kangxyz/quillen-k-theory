/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.CofiberObjectTrack

/-! # Original cofiber-simplex and full object-loop track consumers -/
@[expose] public section

open Quillen.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial Topology
universe u v
namespace QuillenTest.CofiberObjectTrack

open Quillen
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : W.cof i) (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q))

/-- The actual simplex has the original source as its first short face. -/
theorem original_source_face :
    (sSet W.cof W.weq).δ 2 (W.cofiberObjectSimplex i q hi hQ) = W.kZeroObjectSimplex A :=
  W.cofiberObjectSimplex_face i q hi hQ 2

/-- Comparison time zero retains the original source-then-quotient loop. -/
theorem original_initial_track (t : unitInterval) :
    W.cofiberObjectLoopTrack i q hi hQ (0, t) =
      ((W.kZeroObjectLoop A).trans (W.kZeroObjectLoop Q)) t :=
  (W.cofiberObjectLoopTrack i q hi hQ).map_zero_left t

/-- Comparison time one retains the original middle-object loop. -/
theorem original_final_track (t : unitInterval) :
    W.cofiberObjectLoopTrack i q hi hQ (1, t) = W.kZeroObjectLoop B t :=
  (W.cofiberObjectLoopTrack i q hi hQ).map_one_left t

/-- The full original standard-triangle interpolation remains visible at independent times. -/
theorem original_triangle_coordinates (r t : unitInterval) :
    W.cofiberObjectLoopTrack i q hi hQ (r, t) =
      SSet.toTop.map (SSet.yonedaEquiv.symm (W.cofiberObjectSimplex i q hi hQ))
        (realizationStdSimplexPathHomotopy
          ((realizationEdgePath (simplexEdge 2 0 1 (by decide))).trans
            (realizationEdgePath (simplexEdge 2 1 2 (by decide))))
          (realizationEdgePath (simplexEdge 2 0 2 (by decide))) (r, t)) :=
  realizationEdgeCompositionHomotopy_apply (W.cofiberObjectCompStruct i q hi hQ) r t

end QuillenTest.CofiberObjectTrack
