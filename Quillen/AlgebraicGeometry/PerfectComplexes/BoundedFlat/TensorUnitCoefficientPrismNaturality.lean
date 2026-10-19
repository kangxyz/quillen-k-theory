/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientPrism

/-!
# Independent ordinal naturality of the fixed coefficient tensor slice

The actual tensor slice retains the first coefficient S-row, coefficient nerve parameter and
both original second-grid ordinal coordinates. Simultaneous reindexing is an equality of whole
diagrams, not just the middle coefficient map or a K-group operation.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.QuotientRows
open scoped Simplicial
universe u
namespace Quillen.PerfectComplexes

/-- Original second-grid reindexing changes exactly its displayed coefficient nerve parameter. -/
theorem tensorUnitFirstRowPrism_precomp (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m n' m' : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect X)
    (τ : m ⟶ ⦋1⦌) (α : n' ⟶ n) (β : m' ⟶ m) :
    tensorUnitFirstRowPrism X r (gridMap₂ α β ⋙ A) (β ≫ τ) =
      gridMap₂ α β ⋙ tensorUnitFirstRowPrism X r A τ := rfl

/-- The first coefficient row is unchanged by the independent second-grid restrictions. -/
theorem tensorUnitCoefficientPrism_precomp (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {k n m n' m' : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect X)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) (α : n' ⟶ n) (β : m' ⟶ m) :
    tensorUnitCoefficientPrism X r (gridMap₂ α β ⋙ A) (β ≫ τ) θ =
      gridMap₂ α β ⋙ tensorUnitCoefficientPrism X r A τ θ := by
  unfold tensorUnitCoefficientPrism
  rw [tensorUnitFirstRowPrism_precomp]
  rfl

/-- Every first-row, coefficient-nerve and second-input ordinal restriction is retained together.
-/
theorem tensorUnitCoefficientPrism_reindex_all (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {k l n m n' m' : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect X)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) (ρ : l ⟶ k) (α : n' ⟶ n) (β : m' ⟶ m) :
    tensorUnitCoefficientPrism X r (gridMap₂ α β ⋙ A) (β ≫ τ) (ρ ≫ θ) =
      gridMap₂ α β ⋙ tensorUnitCoefficientPrism X r A τ θ ⋙
        reindex (boundedFlatPerfectWaldhausen X) ρ := by
  rw [tensorUnitCoefficientPrism_precomp, tensorUnitCoefficientPrism_reindex]

end Quillen.PerfectComplexes
