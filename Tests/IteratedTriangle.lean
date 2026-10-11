/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.TriangleStructure

/-! Actual iterated triangle faces, whole zero restriction and independent suspension parameter. -/
@[expose] public section

open CategoryTheory Opposite MonoidalCategory Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open scoped Simplicial
universe u

namespace Quillen.Tests.IteratedTriangle

variable {V W : Model.{u}} {F G H : V ⟶ W}
  (η : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
  (hη : ∀ A, W.waldhausen.weq (η.app A)) (hθ : ∀ A, W.waldhausen.weq (θ.app A))

lemma original_first_face (r : ℕ) :
    ((𝟙 ((stages r).obj V)) ⊗ₘ SSet.stdSimplex.δ 2) ≫
        stageTransformationTriangle r η θ hη hθ = stageTransformationCylinder r η hη :=
  stageTransformationTriangle_first η θ hη hθ r

lemma original_second_face (r : ℕ) :
    ((𝟙 ((stages r).obj V)) ⊗ₘ SSet.stdSimplex.δ 0) ≫
        stageTransformationTriangle r η θ hη hθ = stageTransformationCylinder r θ hθ :=
  stageTransformationTriangle_second η θ hη hθ r

lemma original_composite_face (r : ℕ) :
    ((𝟙 ((stages r).obj V)) ⊗ₘ SSet.stdSimplex.δ 1) ≫
        stageTransformationTriangle r η θ hη hθ =
      stageTransformationCylinder r (η ≫ θ)
        (fun A ↦ W.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)) :=
  stageTransformationTriangle_composite η θ hη hθ r

lemma original_zero_triangle (r : ℕ) :
    SSet.yonedaEquiv.symm (stageVertex r V) ▷ Δ[2] ≫ stageTransformationTriangle r η θ hη hθ =
      CartesianMonoidalCategory.fst Δ[0] Δ[2] ≫ SSet.yonedaEquiv.symm (stageVertex r W) :=
  stageTransformationTriangle_fixed_vertex η θ hη hθ r

lemma independent_triangle_and_suspension (r : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj V).obj n) (τ : (Δ[1]).obj n) (σ : (Δ[2]).obj n) :
    stageTriangleFunction (r + 1) η θ hη hθ n ((stageCylinder r V).app n (A, τ)) σ =
      (stageCylinder r W).app n (stageTriangleFunction r η θ hη hθ n A σ, τ) :=
  stageTriangleFunction_structure r η θ hη hθ n A τ σ

end Quillen.Tests.IteratedTriangle
