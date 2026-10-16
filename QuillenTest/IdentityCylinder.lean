/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.IdentityCylinder

/-! Whole grids, crossing morphisms, independent reindexings and actual realized identity time. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory Quillen Quillen.Waldhausen
open scoped Simplicial Topology
universe u v
namespace QuillenTest.IdentityCylinder
variable {D : Type u} [Category.{v} D]

/-- Every original cut retains the entire original grid, not just its two endpoint rows. -/
theorem original_whole_grid {n m : SimplexCategory} (A : Grid₂ n m ⥤ D)
    (τ : m ⟶ ⦋1⦌) : nerveCylinderDiagram (𝟙 A) τ = A :=
  nerveCylinderDiagram_identity A τ

/-- Every original morphism, including crossing arrows, keeps the two actual object casts. -/
theorem original_whole_morphism {n m : SimplexCategory} (A : Grid₂ n m ⥤ D)
    (τ : m ⟶ ⦋1⦌) {p q : Grid₂ n m} (f : p ⟶ q) :
    eqToHom (congrArg (fun T ↦ T.obj p) (nerveCylinderDiagram_identity A τ)).symm ≫
        (nerveCylinderDiagram (𝟙 A) τ).map f ≫
        eqToHom (congrArg (fun T ↦ T.obj q) (nerveCylinderDiagram_identity A τ)) = A.map f :=
  nerveCylinderDiagram_identity_map A τ f

/-- Both original degree restrictions and their transformed cut vary independently. -/
theorem original_independent_reindex {n n' m m' : SimplexCategory}
    (A : Grid₂ n m ⥤ D) (α : n' ⟶ n) (β : m' ⟶ m) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram (𝟙 (gridMap₂ α β ⋙ A)) (β ≫ τ) =
      gridMap₂ α β ⋙ nerveCylinderDiagram (𝟙 A) τ :=
  nerveCylinderDiagram_identity_reindex A α β τ

variable (W : Structure D) {X : SimplexCategoryᵒᵖ ⥤ SSet.{max u v}}
  (f : X ⟶ bisimplicialSSet W)

/-- The actual old weak-grid cylinder retains the complete first projection. -/
theorem original_simplicial_cylinder :
    (diagonalWeakGridIdentityHomotopy W f).h =
      CartesianMonoidalCategory.fst (TheoremA.diagonalSSet X) Δ[1] ≫
        TheoremA.diagonalMap f :=
  diagonalWeakGridIdentityHomotopy_cylinder W f

/-- Both the original input and the full identity time remain explicit after realization. -/
theorem original_realization_time (t : unitInterval) (x : |TheoremA.diagonalSSet X|) :
    realizationSimplicialHomotopy (diagonalWeakGridIdentityHomotopy W f) (t, x) =
      SSet.toTop.map (TheoremA.diagonalMap f) x :=
  diagonalWeakGridIdentityHomotopy_realization W f t x

/-- An original degree-zero simplex keeps the same whole identity time. -/
theorem original_zero_simplex (t : unitInterval)
    (x : (TheoremA.diagonalSSet X) _⦋0⦌) :
    realizationSimplicialHomotopy (diagonalWeakGridIdentityHomotopy W f)
        (t, realizationPoint x) =
      SSet.toTop.map (TheoremA.diagonalMap f) (realizationPoint x) :=
  diagonalWeakGridIdentityHomotopy_realization W f t (realizationPoint x)

end QuillenTest.IdentityCylinder
