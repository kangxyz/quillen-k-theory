/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.NerveTriangle

/-! Actual distinct triangle faces, weak-grid membership, reindexing
and literal zero restriction. -/
@[expose] public section

open Quillen.Waldhausen


open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped Simplicial

universe u v

namespace QuillenTest.NerveTriangle

open Quillen

variable {D : Type u} [Category.{v} D] {n m : SimplexCategory}
  {A B C : Grid₂ n m ⥤ D} (η : A ⟶ B) (θ : B ⟶ C)

lemma original_first_face (τ : m ⟶ ⦋1⦌) :
    nerveTriangleDiagram η θ (τ ≫ SimplexCategory.δ 2) = nerveCylinderDiagram η τ :=
  nerveTriangleDiagram_first η θ τ

lemma original_second_face (τ : m ⟶ ⦋1⦌) :
    nerveTriangleDiagram η θ (τ ≫ SimplexCategory.δ 0) = nerveCylinderDiagram θ τ :=
  nerveTriangleDiagram_second η θ τ

lemma original_composite_face (τ : m ⟶ ⦋1⦌) :
    nerveTriangleDiagram η θ (τ ≫ SimplexCategory.δ 1) = nerveCylinderDiagram (η ≫ θ) τ :=
  nerveTriangleDiagram_composite η θ τ

lemma original_weak_grid (W : Structure D)
    (hη : ∀ p, W.weq (η.app p)) (hθ : ∀ p, W.weq (θ.app p))
    (hA : IsSimplex₂ W.cof W.weq A) (hB : IsSimplex₂ W.cof W.weq B)
    (hC : IsSimplex₂ W.cof W.weq C) (τ : m ⟶ ⦋2⦌) :
    IsSimplex₂ W.cof W.weq (nerveTriangleDiagram η θ τ) :=
  nerveTriangleDiagram_isSimplex₂ W η θ hη hθ hA hB hC τ

lemma original_zero_restriction (Z : D) (hZ : IsZero Z)
    (hA : ∀ p, A.obj p = Z) (hB : ∀ p, B.obj p = Z) (hC : ∀ p, C.obj p = Z)
    (τ : m ⟶ ⦋2⦌) : nerveTriangleDiagram η θ τ = (Functor.const (Grid₂ n m)).obj Z :=
  nerveTriangleDiagram_eq_const_of_zero η θ Z hZ hA hB hC τ

lemma independent_grid_coordinates {n' m' : SimplexCategory}
    (α : n' ⟶ n) (β : m' ⟶ m) (τ : m ⟶ ⦋2⦌) :
    nerveTriangleDiagram (whiskerLeft (gridMap₂ α β) η)
      (whiskerLeft (gridMap₂ α β) θ) (β ≫ τ) =
      gridMap₂ α β ⋙ nerveTriangleDiagram η θ τ :=
  nerveTriangleDiagram_precomp η θ α β τ

end QuillenTest.NerveTriangle
