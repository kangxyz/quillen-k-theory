/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! # Cokernels of split graph columns

In any preadditive category with binary products, the columns `(1, f)` and `(f, 1)`
have the displayed cokernel rows `(-f, 1)` and `(-1, f)`. The universal properties
retain these literal rows and their explicit sections.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe v u
namespace Quillen
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryProducts C]
  {A B : C} (f : A ⟶ B)

/-- The graph inclusion with ordered components `(1, f)`. -/
def graphColumn : A ⟶ A ⨯ B := prod.lift (𝟙 A) f

/-- The signed row `(-f, 1)` that annihilates the graph inclusion. -/
def graphRow : A ⨯ B ⟶ B := prod.snd - prod.fst ≫ f

/-- The second-coordinate section of the graph quotient row. -/
def graphSection : B ⟶ A ⨯ B := prod.lift 0 (𝟙 B)

/-- The graph inclusion is annihilated by its signed row. -/
lemma graphColumn_row : graphColumn f ≫ graphRow f = 0 := by
  simp [graphColumn, graphRow, Preadditive.comp_sub]

/-- The second-coordinate inclusion splits the signed row. -/
lemma graphSection_row : graphSection (A := A) (B := B) ≫ graphRow f = 𝟙 B := by
  simp [graphSection, graphRow, Preadditive.comp_sub]

/-- The original product identity decomposes along its graph and quotient. -/
lemma graph_decomposition :
    prod.fst ≫ graphColumn f + graphRow f ≫ graphSection (A := A) (B := B) = 𝟙 (A ⨯ B) := by
  apply prod.hom_ext
  · simp [graphColumn, graphRow, graphSection, Preadditive.add_comp]
  · simp [graphColumn, graphRow, graphSection, Preadditive.add_comp]

/-- The signed graph row satisfies the actual cokernel universal property. -/
def graphRowIsCokernel : IsColimit (CokernelCofork.ofπ (graphRow f) (graphColumn_row f)) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨graphSection (A := A) (B := B) ≫ s.π, by
      change graphRow f ≫ (graphSection (A := A) (B := B) ≫ s.π) = s.π
      have h := congrArg (fun k => k ≫ s.π) (graph_decomposition f)
      simpa only [Preadditive.add_comp, Category.assoc, CokernelCofork.condition,
        comp_zero, zero_add, Category.id_comp] using h,
    by
      intro m hm
      change graphRow f ≫ m = s.π at hm
      rw [← hm, ← Category.assoc, graphSection_row, Category.id_comp]⟩

/-- The graph inclusion with the two coordinates exchanged. -/
def cographColumn : A ⟶ B ⨯ A := prod.lift f (𝟙 A)

/-- The signed row `(-1, f)` for the exchanged graph inclusion. -/
def cographRow : B ⨯ A ⟶ B := prod.snd ≫ f - prod.fst

/-- The negative first-coordinate section of the exchanged quotient row. -/
def cographSection : B ⟶ B ⨯ A := prod.lift (-𝟙 B) 0

/-- The exchanged graph inclusion is annihilated by its signed row. -/
lemma cographColumn_row : cographColumn f ≫ cographRow f = 0 := by
  simp [cographColumn, cographRow, Preadditive.comp_sub]

/-- The negative first-coordinate inclusion splits the exchanged row. -/
lemma cographSection_row : cographSection (A := A) (B := B) ≫ cographRow f = 𝟙 B := by
  simp [cographSection, cographRow, Preadditive.comp_sub]

/-- The product identity decomposes along the exchanged graph and quotient. -/
lemma cograph_decomposition :
    prod.snd ≫ cographColumn f + cographRow f ≫ cographSection (A := A) (B := B) =
      𝟙 (B ⨯ A) := by
  apply prod.hom_ext
  · simp [cographColumn, cographRow, cographSection, Preadditive.add_comp]
  · simp [cographColumn, cographRow, cographSection, Preadditive.add_comp]

/-- The exchanged signed row satisfies the actual cokernel universal property. -/
def cographRowIsCokernel :
    IsColimit (CokernelCofork.ofπ (cographRow f) (cographColumn_row f)) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨cographSection (A := A) (B := B) ≫ s.π, by
      change cographRow f ≫ (cographSection (A := A) (B := B) ≫ s.π) = s.π
      have h := congrArg (fun k => k ≫ s.π) (cograph_decomposition f)
      simpa only [Preadditive.add_comp, Category.assoc, CokernelCofork.condition,
        comp_zero, zero_add, Category.id_comp] using h,
    by
      intro m hm
      change cographRow f ≫ m = s.π at hm
      rw [← hm, ← Category.assoc, cographSection_row, Category.id_comp]⟩

end Quillen
