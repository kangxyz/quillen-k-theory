/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.WeakGridSquare

/-! # Whole original weak-grid square faces and chosen-zero simplices -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory Quillen Quillen.Waldhausen
open scoped Simplicial
universe v u
namespace QuillenTest.WeakGridSquare
variable {D : Type u} [Category.{v} D] (W : Structure D)
  {X : SimplexCategoryᵒᵖ ⥤ SSet.{max u v}}
  (f00 f01 f10 f11 : X ⟶ bisimplicialSSet W)
  (α : ∀ (n m : SimplexCategoryᵒᵖ) (x : (X.obj n).obj m),
    (((f00.app n).app m) x).1 ⟶ (((f01.app n).app m) x).1)
  (α' : ∀ (n m : SimplexCategoryᵒᵖ) (x : (X.obj n).obj m),
    (((f10.app n).app m) x).1 ⟶ (((f11.app n).app m) x).1)
  (β : ∀ (n m : SimplexCategoryᵒᵖ) (x : (X.obj n).obj m),
    (((f00.app n).app m) x).1 ⟶ (((f10.app n).app m) x).1)
  (δ : ∀ (n m : SimplexCategoryᵒᵖ) (x : (X.obj n).obj m),
    (((f01.app n).app m) x).1 ⟶ (((f11.app n).app m) x).1)
  (h : ∀ n m x, α n m x ≫ δ n m x = β n m x ≫ α' n m x)
  (hα : ∀ n m x p, W.weq ((α n m x).app p))
  (hα' : ∀ n m x p, W.weq ((α' n m x).app p))
  (hβ : ∀ n m x p, W.weq ((β n m x).app p))
  (hδ : ∀ n m x p, W.weq ((δ n m x).app p))
  (hcompatα : ∀ {n n' : SimplexCategoryᵒᵖ} (ρ : n ⟶ n')
    (x : (TheoremA.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop),
    HEq ((α n' n' ((TheoremA.diagonalSSet X).map ρ x)).app p)
      ((α n n x).app ((gridMap₂ ρ.unop ρ.unop).obj p)))
  (hcompatα' : ∀ {n n' : SimplexCategoryᵒᵖ} (ρ : n ⟶ n')
    (x : (TheoremA.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop),
    HEq ((α' n' n' ((TheoremA.diagonalSSet X).map ρ x)).app p)
      ((α' n n x).app ((gridMap₂ ρ.unop ρ.unop).obj p)))
  (hcompatβ : ∀ {n n' : SimplexCategoryᵒᵖ} (ρ : n ⟶ n')
    (x : (TheoremA.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop),
    HEq ((β n' n' ((TheoremA.diagonalSSet X).map ρ x)).app p)
      ((β n n x).app ((gridMap₂ ρ.unop ρ.unop).obj p)))
  (hcompatδ : ∀ {n n' : SimplexCategoryᵒᵖ} (ρ : n ⟶ n')
    (x : (TheoremA.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop),
    HEq ((δ n' n' ((TheoremA.diagonalSSet X).map ρ x)).app p)
      ((δ n n x).app ((gridMap₂ ρ.unop ρ.unop).obj p)))

/-- All four entire faces retain their exact old cylinders. -/
theorem four_original_cylinders :
    SSet.ι₀ ≫ weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ =
        weakGridFamilyCylinder W f00 f01 α hα hcompatα ∧
      SSet.ι₁ ≫ weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ =
        weakGridFamilyCylinder W f10 f11 α' hα' hcompatα' ∧
      (SSet.ι₀ ▷ Δ[1]) ≫ weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ =
        weakGridFamilyCylinder W f00 f10 β hβ hcompatβ ∧
      (SSet.ι₁ ▷ Δ[1]) ≫ weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ =
        weakGridFamilyCylinder W f01 f11 δ hδ hcompatδ :=
  ⟨weakGridFamilySquare_vertical_zero W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ,
    weakGridFamilySquare_vertical_one W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ,
    weakGridFamilySquare_horizontal_zero W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ,
    weakGridFamilySquare_horizontal_one W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ⟩

variable (x : (TheoremA.diagonalSSet X) _⦋0⦌)
  (hf00 : ∀ (n : SimplexCategoryᵒᵖ) (z : (Δ[0] : SSet.{max u v}).obj n) p,
    ((((f00.app n).app n) ((SSet.yonedaEquiv.symm x).app n z)).1.obj p) = W.zero)
  (hf01 : ∀ (n : SimplexCategoryᵒᵖ) (z : (Δ[0] : SSet.{max u v}).obj n) p,
    ((((f01.app n).app n) ((SSet.yonedaEquiv.symm x).app n z)).1.obj p) = W.zero)
  (hf10 : ∀ (n : SimplexCategoryᵒᵖ) (z : (Δ[0] : SSet.{max u v}).obj n) p,
    ((((f10.app n).app n) ((SSet.yonedaEquiv.symm x).app n z)).1.obj p) = W.zero)
  (hf11 : ∀ (n : SimplexCategoryᵒᵖ) (z : (Δ[0] : SSet.{max u v}).obj n) p,
    ((((f11.app n).app n) ((SSet.yonedaEquiv.symm x).app n z)).1.obj p) = W.zero)


include hf00 hf01 hf10 hf11 in
/-- Every degenerate input simplex remains constant in the complete original two-time square. -/
theorem whole_zero_simplex :
    ((SSet.yonedaEquiv.symm x ▷ Δ[1]) ▷ Δ[1]) ≫
      weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ =
      CartesianMonoidalCategory.fst (Δ[0] ⊗ Δ[1]) Δ[1] ≫
        CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫
          SSet.yonedaEquiv.symm (diagonalZeroVertex W) :=
  weakGridFamilySquare_fixed_vertex W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ x hf00 hf01 hf10 hf11

end QuillenTest.WeakGridSquare
