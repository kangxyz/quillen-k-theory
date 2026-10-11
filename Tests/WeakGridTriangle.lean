/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.WeakGridTriangle

/-! Consumers of the actual Δ[2] family, retaining original components and zero grids. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open Quillen Quillen.Waldhausen
open scoped Simplicial
universe v u

namespace Quillen.Tests.WeakGridTriangle

variable {D : Type u} [Category.{v} D] (W : Structure D)
  {X : SimplexCategoryᵒᵖ ⥤ SSet.{max u v}}
  (f g h : X ⟶ bisimplicialSSet W)
  (η : ∀ (n m : SimplexCategoryᵒᵖ) (x : (X.obj n).obj m),
    (((f.app n).app m) x).1 ⟶ (((g.app n).app m) x).1)
  (θ : ∀ (n m : SimplexCategoryᵒᵖ) (x : (X.obj n).obj m),
    (((g.app n).app m) x).1 ⟶ (((h.app n).app m) x).1)
  (hη : ∀ n m x p, W.weq ((η n m x).app p))
  (hθ : ∀ n m x p, W.weq ((θ n m x).app p))
  (hcompatη : ∀ {n n' : SimplexCategoryᵒᵖ} (α : n ⟶ n')
    (x : (TheoremA.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop),
    HEq ((η n' n' ((TheoremA.diagonalSSet X).map α x)).app p)
      ((η n n x).app ((gridMap₂ α.unop α.unop).obj p)))
  (hcompatθ : ∀ {n n' : SimplexCategoryᵒᵖ} (α : n ⟶ n')
    (x : (TheoremA.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop),
    HEq ((θ n' n' ((TheoremA.diagonalSSet X).map α x)).app p)
      ((θ n n x).app ((gridMap₂ α.unop α.unop).obj p)))

lemma original_whole_triangle (n : SimplexCategoryᵒᵖ)
    (x : (TheoremA.diagonalSSet X).obj n) (τ : (Δ[2]).obj n) :
    (((weakGridFamilyTriangle W f g h η θ hη hθ hcompatη hcompatθ).app n) (x, τ)).val =
      nerveTriangleDiagram (η n n x) (θ n n x) τ.down := rfl

lemma original_first_face (n : SimplexCategoryᵒᵖ)
    (x : (TheoremA.diagonalSSet X).obj n) (τ : n.unop ⟶ ⦋1⦌) :
    (((weakGridFamilyTriangle W f g h η θ hη hθ hcompatη hcompatθ).app n)
      (x, ⟨τ ≫ SimplexCategory.δ 2⟩)).val = nerveCylinderDiagram (η n n x) τ :=
  nerveTriangleDiagram_first (η n n x) (θ n n x) τ

lemma original_second_face (n : SimplexCategoryᵒᵖ)
    (x : (TheoremA.diagonalSSet X).obj n) (τ : n.unop ⟶ ⦋1⦌) :
    (((weakGridFamilyTriangle W f g h η θ hη hθ hcompatη hcompatθ).app n)
      (x, ⟨τ ≫ SimplexCategory.δ 0⟩)).val = nerveCylinderDiagram (θ n n x) τ :=
  nerveTriangleDiagram_second (η n n x) (θ n n x) τ

lemma original_composite_face (n : SimplexCategoryᵒᵖ)
    (x : (TheoremA.diagonalSSet X).obj n) (τ : n.unop ⟶ ⦋1⦌) :
    (((weakGridFamilyTriangle W f g h η θ hη hθ hcompatη hcompatθ).app n)
      (x, ⟨τ ≫ SimplexCategory.δ 1⟩)).val = nerveCylinderDiagram (η n n x ≫ θ n n x) τ :=
  nerveTriangleDiagram_composite (η n n x) (θ n n x) τ

lemma original_zero_grid (n : SimplexCategoryᵒᵖ) (x : (TheoremA.diagonalSSet X).obj n)
    (Z : D) (hZ : IsZero Z)
    (hf : ∀ p, ((((f.app n).app n) x).val).obj p = Z)
    (hg : ∀ p, ((((g.app n).app n) x).val).obj p = Z)
    (hh : ∀ p, ((((h.app n).app n) x).val).obj p = Z) (τ : (Δ[2]).obj n) :
    (((weakGridFamilyTriangle W f g h η θ hη hθ hcompatη hcompatθ).app n) (x, τ)).val =
      (Functor.const (Grid₂ n.unop n.unop)).obj Z :=
  nerveTriangleDiagram_eq_const_of_zero (η n n x) (θ n n x) Z hZ hf hg hh τ.down

end Quillen.Tests.WeakGridTriangle
