/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.WeakGridSquareRealization
public import QuillenTest.WeakGridSquare

/-! # Original realized weak-grid faces and both independent zero times -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory Quillen Quillen.Waldhausen
open scoped Simplicial Topology unitInterval
universe v u
namespace QuillenTest.WeakGridSquareRealization
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

/-- All four continuous faces retain the original path parametrizations and input. -/
theorem four_original_realized_faces (t s : unitInterval)
    (x : |TheoremA.diagonalSSet X|) :
    diagonalWeakGridRealizationSquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ (0, (s, x)) =
        diagonalWeakGridRealizationHomotopy W f00 f01 α hα hcompatα (s, x) ∧
      diagonalWeakGridRealizationSquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ (1, (s, x)) =
        diagonalWeakGridRealizationHomotopy W f10 f11 α' hα' hcompatα' (s, x) ∧
      diagonalWeakGridRealizationSquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ (t, (0, x)) =
        diagonalWeakGridRealizationHomotopy W f00 f10 β hβ hcompatβ (t, x) ∧
      diagonalWeakGridRealizationSquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ (t, (1, x)) =
        diagonalWeakGridRealizationHomotopy W f01 f11 δ hδ hcompatδ (t, x) :=
  ⟨diagonalWeakGridRealizationSquare_vertical_zero W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ s x,
    diagonalWeakGridRealizationSquare_vertical_one W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ s x,
    diagonalWeakGridRealizationSquare_horizontal_zero W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ t x,
    diagonalWeakGridRealizationSquare_horizontal_one W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ t x⟩

/-- The chosen realization evaluates exactly the two old inverse cylinders. -/
theorem original_two_cylinders (t s : unitInterval) (x : |TheoremA.diagonalSSet X|) :
    diagonalWeakGridRealizationSquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ (t, (s, x)) =
      SSet.toTop.map (weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ)
        ((realizationCylinderIso (TheoremA.diagonalSSet X ⊗ Δ[1])).inv
          ((realizationCylinderIso (TheoremA.diagonalSSet X)).inv
            (x, ULift.up s), ULift.up t)) :=
  diagonalWeakGridRealizationSquare_apply W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ t s x

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
/-- Both continuous times fix the actual vertex from all four original zero grids. -/
theorem whole_zero_realization (t s : unitInterval) :
    diagonalWeakGridRealizationSquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ (t, (s, realizationPoint x)) =
      realizationPoint (diagonalZeroVertex W) :=
  diagonalWeakGridRealizationSquare_fixed_vertex W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ x hf00 hf01 hf10 hf11 t s

end QuillenTest.WeakGridSquareRealization
