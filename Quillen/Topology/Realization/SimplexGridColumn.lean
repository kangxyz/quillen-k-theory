/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Topology.Realization.SimplexGridBoundary

/-! Whole column restrictions of the actual realization-product parameter. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Simplicial Topology
universe u
namespace Quillen.SimplexGrid

def columnFace (p q : ℕ) (j : Fin (q + 1)) : ⦋p⦌ ⟶ ⦋dimension p q⦌ :=
  SimplexCategory.Hom.mk ⟨fun i ↦ index p q (i, j),
    fun _ _ h ↦ (index p q).monotone ⟨h, le_rfl⟩⟩

def column (p q : ℕ) (j : Fin (q + 1)) : (Δ[p] : SSet.{u}) ⟶ Δ[p] ⊗ Δ[q] :=
  lift (𝟙 _) (SSet.stdSimplex.map (constantFace j))

theorem column_embedding (p q : ℕ) (j : Fin (q + 1)) :
    column.{u} p q j ≫ embedding p q = SSet.stdSimplex.map (columnFace p q j) := by
  ext n z : 4
  rfl

/-- The actual product homeomorphism restricts to the literal fixed column. -/
theorem homeomorph_column (p q : ℕ) (j : Fin (q + 1)) (w : |(Δ[p] : SSet.{u})|) :
    realizationProductSimplexHomeomorph p q (SSet.toTop.map (column p q j) w) =
      (SimplexCategory.toTopHomeo ⦋p⦌ w, StdSimplex.single j) := by
  rw [realizationProductSimplexHomeomorph_apply]
  apply Prod.ext
  · change SimplexCategory.toTopHomeo ⦋p⦌
      ((SSet.toTop.map (column p q j) ≫ SSet.toTop.map (fst Δ[p] Δ[q])) w) = _
    rw [← Functor.map_comp]
    change SimplexCategory.toTopHomeo ⦋p⦌
      (SSet.toTop.map (lift (𝟙 _) (SSet.stdSimplex.map (constantFace j)) ≫ fst _ _) w) = _
    rw [lift_fst, CategoryTheory.Functor.map_id]
    rfl
  · change SimplexCategory.toTopHomeo ⦋q⦌
      ((SSet.toTop.map (column p q j) ≫ SSet.toTop.map (snd Δ[p] Δ[q])) w) = _
    rw [← Functor.map_comp]
    change SimplexCategory.toTopHomeo ⦋q⦌
      (SSet.toTop.map (lift (𝟙 _) (SSet.stdSimplex.map (constantFace j)) ≫ snd _ _) w) = _
    rw [lift_snd, SimplexCategory.toTopHomeo_naturality_apply]
    exact StdSimplex.map_const _ j

/-- The whole actual column parameter equals its affine simplex face, with no weight assumption. -/
theorem parameter_column (p q : ℕ) (j : Fin (q + 1)) (w : StdSimplex ℝ (Fin (p + 1))) :
    parameter.{u} p q (w, StdSimplex.single j) =
      StdSimplex.map (columnFace p q j).toOrderHom w := by
  have h := parameter_realization p q
    (SSet.toTop.map (column.{u} p q j) ((SimplexCategory.toTopHomeo ⦋p⦌).symm w))
  rw [homeomorph_column, Homeomorph.apply_symm_apply] at h
  change parameter p q (w, StdSimplex.single j) =
    SimplexCategory.toTopHomeo ⦋dimension p q⦌
      ((SSet.toTop.map (column p q j) ≫ SSet.toTop.map (embedding p q))
        ((SimplexCategory.toTopHomeo ⦋p⦌).symm w)) at h
  rw [← Functor.map_comp, column_embedding, SimplexCategory.toTopHomeo_naturality_apply,
    Homeomorph.apply_symm_apply] at h
  exact h

end Quillen.SimplexGrid
