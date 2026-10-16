/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.NerveSquareNaturality

/-! # Consumers of both independent nerve times and the original four edges -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Quillen.Waldhausen
open scoped Simplicial
universe v u
namespace QuillenTest.NerveSquare
variable {D : Type u} [Category.{v} D] {n m : SimplexCategory}
variable {A B A' B' : Grid₂ n m ⥤ D}
variable (α : A ⟶ B) (α' : A' ⟶ B') (β : A ⟶ A') (δ : B ⟶ B')
variable (h : α ≫ δ = β ≫ α')

/-- All four original edge cylinders are retained, with two independently supplied times. -/
theorem four_actual_edges (τ σ : m ⟶ ⦋1⦌) :
    nerveSquareDiagram α α' β δ h τ (SimplexCategory.const m ⦋1⦌ 0) =
        nerveCylinderDiagram α τ ∧
      nerveSquareDiagram α α' β δ h τ (SimplexCategory.const m ⦋1⦌ 1) =
        nerveCylinderDiagram α' τ ∧
      nerveSquareDiagram α α' β δ h (SimplexCategory.const m ⦋1⦌ 0) σ =
        nerveCylinderDiagram β σ ∧
      nerveSquareDiagram α α' β δ h (SimplexCategory.const m ⦋1⦌ 1) σ =
        nerveCylinderDiagram δ σ :=
  ⟨nerveSquareDiagram_vertical_zero α α' β δ h τ,
    nerveSquareDiagram_vertical_one α α' β δ h τ,
    nerveSquareDiagram_horizontal_zero α α' β δ h σ,
    nerveSquareDiagram_horizontal_one α α' β δ h σ⟩

/-- Reindexing changes both actual times by the same supplied nerve map, independently of S-time. -/
theorem original_grid_reindex {n' m' : SimplexCategory}
    (μ : n' ⟶ n) (ν : m' ⟶ m) (τ σ : m ⟶ ⦋1⦌) :
    nerveSquareDiagram (whiskerLeft (gridMap₂ μ ν) α)
      (whiskerLeft (gridMap₂ μ ν) α') (whiskerLeft (gridMap₂ μ ν) β)
      (whiskerLeft (gridMap₂ μ ν) δ) (nerveSquare_reindex_comm α α' β δ h μ ν)
      (ν ≫ τ) (ν ≫ σ) = gridMap₂ μ ν ⋙ nerveSquareDiagram α α' β δ h τ σ :=
  nerveSquareDiagram_precomp α α' β δ h μ ν τ σ

/-- Actual zero corner diagrams fix every point of the entire square. -/
theorem whole_zero_square (Z : D) (hZ : IsZero Z)
    (hA : ∀ p, A.obj p = Z) (hB : ∀ p, B.obj p = Z)
    (hA' : ∀ p, A'.obj p = Z) (hB' : ∀ p, B'.obj p = Z)
    (τ σ : m ⟶ ⦋1⦌) :
    nerveSquareDiagram α α' β δ h τ σ = (Functor.const (Grid₂ n m)).obj Z :=
  nerveSquareDiagram_eq_const_of_zero α α' β δ h Z hZ hA hB hA' hB' τ σ

end QuillenTest.NerveSquare
