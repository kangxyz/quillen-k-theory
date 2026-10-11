/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.WeakNaturalTransformationTriangle

/-! Consumers of the actual exact-functor triangle and its entire chosen-zero restriction. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open Quillen Quillen.Waldhausen
open scoped Simplicial
universe v u

namespace Quillen.Tests.WeakNaturalTransformationTriangle

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G H : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (hH : IsExact V.cof V.weq W.cof W.weq H)
  (η : F ⟶ G) (θ : G ⟶ H)
  (hη : ∀ X, W.weq (η.app X)) (hθ : ∀ X, W.weq (θ.app X))

lemma original_grid_components (n : SimplexCategoryᵒᵖ)
    (x : (sSet V.cof V.weq).obj n) (τ : (Δ[2]).obj n) :
    ((weakNaturalTransformationTriangle V W hF hG hH η θ hη hθ).app n (x, τ)).val =
      nerveTriangleDiagram (whiskerLeft x.val η) (whiskerLeft x.val θ) τ.down := rfl

lemma original_first_face :
    ((𝟙 (sSet V.cof V.weq)) ⊗ₘ SSet.stdSimplex.δ 2) ≫
        weakNaturalTransformationTriangle V W hF hG hH η θ hη hθ =
      weakNaturalTransformationCylinder V W hF hG η hη :=
  weakNaturalTransformationTriangle_first V W hF hG hH η θ hη hθ

lemma original_second_face :
    ((𝟙 (sSet V.cof V.weq)) ⊗ₘ SSet.stdSimplex.δ 0) ≫
        weakNaturalTransformationTriangle V W hF hG hH η θ hη hθ =
      weakNaturalTransformationCylinder V W hG hH θ hθ :=
  weakNaturalTransformationTriangle_second V W hF hG hH η θ hη hθ

lemma original_composite_face :
    ((𝟙 (sSet V.cof V.weq)) ⊗ₘ SSet.stdSimplex.δ 1) ≫
        weakNaturalTransformationTriangle V W hF hG hH η θ hη hθ =
      weakNaturalTransformationCylinder V W hF hH (η ≫ θ)
        (fun X ↦ W.weq.comp_mem _ _ (hη X) (hθ X)) :=
  weakNaturalTransformationTriangle_composite V W hF hG hH η θ hη hθ

lemma original_zero_triangle (hF0 : F.obj V.zero = W.zero) (hG0 : G.obj V.zero = W.zero)
    (hH0 : H.obj V.zero = W.zero) :
    SSet.yonedaEquiv.symm (zeroSimplex V.cof V.weq V.zero V.isZero (op ⦋0⦌)) ▷ Δ[2] ≫
        weakNaturalTransformationTriangle V W hF hG hH η θ hη hθ =
      CartesianMonoidalCategory.fst Δ[0] Δ[2] ≫
        SSet.yonedaEquiv.symm (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) :=
  weakNaturalTransformationTriangle_fixed_zero V W hF hG hH η θ hη hθ hF0 hG0 hH0

end Quillen.Tests.WeakNaturalTransformationTriangle
