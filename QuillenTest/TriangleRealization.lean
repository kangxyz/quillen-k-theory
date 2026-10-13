/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.TriangleRealization

/-! The actual Δ[2]/interval swap and original iterated-stage structure map. -/
@[expose] public section

noncomputable section
open CategoryTheory MonoidalCategory Quillen Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u

namespace QuillenTest.TriangleRealization

open Quillen

lemma original_mixed_coordinates (X : SSet.{u}) (x : |X|)
    (t : TopCat.I.{u}) (z : |(Δ[2] : SSet.{u})|) :
    SSet.toTop.map (simplicialSimplexCylinderSwap X 2)
      ((realizationProductSimplexIso (X ⊗ Δ[1]) 2).inv
        ((realizationCylinderIso X).inv (x, t), z)) =
      (realizationCylinderIso (X ⊗ Δ[2])).inv
        ((realizationProductSimplexIso X 2).inv (x, z), t) :=
  realizationSimplexCylinderSwap_inv X 2 x t z

variable {V W : Model.{u}} {F G H : V ⟶ W}
  (η : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
  (hη : ∀ A, W.waldhausen.weq (η.app A)) (hθ : ∀ A, W.waldhausen.weq (θ.app A))

lemma original_triangle_family (r : ℕ) (x : stageSpace r V) (z : |(Δ[2] : SSet.{u})|) :
    stageTriangleRealization η θ hη hθ r (x, z) =
      SSet.toTop.map (stageTransformationTriangle r η θ hη hθ)
        ((realizationProductSimplexIso ((stages r).obj V) 2).inv (x, z)) := rfl

lemma original_independent_structure (r : ℕ)
    (x : stageSpace r V) (z : |(Δ[2] : SSet.{u})|) (t : unitInterval) :
    stageTriangleRealization η θ hη hθ (r + 1) (stageLoopMap r V x t, z) =
      stageLoopMap r W (stageTriangleRealization η θ hη hθ r (x, z)) t :=
  stageTriangleRealization_structure η θ hη hθ r z t x

end QuillenTest.TriangleRealization
