/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Topology.Realization.SimplexProductParameter

/-! Exact row restrictions of the actual product-realization parameter. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Simplicial Topology
universe u
namespace Quillen.SimplexGrid

/-- The simplex map sending every vertex of the source simplex to vertex `i`. -/
def constantFace {p q : ℕ} (i : Fin (p + 1)) : ⦋q⦌ ⟶ ⦋p⦌ :=
  SimplexCategory.Hom.mk ⟨fun _ ↦ i, fun _ _ _ ↦ le_rfl⟩

/-- The simplex map selecting grid vertices `(i, j)` with first coordinate fixed to `i`. -/
def rowFace (p q : ℕ) (i : Fin (p + 1)) : ⦋q⦌ ⟶ ⦋dimension p q⦌ :=
  SimplexCategory.Hom.mk ⟨fun j ↦ index p q (i, j),
    fun _ _ h ↦ (index p q).monotone ⟨le_rfl, h⟩⟩

/-- The simplicial inclusion of the row with first coordinate equal to vertex `i` and second
coordinate varying in `Δ[q]`.
-/
def row (p q : ℕ) (i : Fin (p + 1)) : (Δ[q] : SSet.{u}) ⟶ Δ[p] ⊗ Δ[q] :=
  lift (SSet.stdSimplex.map (constantFace i)) (𝟙 _)

theorem row_embedding (p q : ℕ) (i : Fin (p + 1)) :
    row.{u} p q i ≫ embedding p q = SSet.stdSimplex.map (rowFace p q i) := by
  ext n z : 4
  rfl

/-- The product homeomorphism identifies the simplicial row with the literal fixed vertex. -/
theorem homeomorph_row (p q : ℕ) (i : Fin (p + 1)) (w : |(Δ[q] : SSet.{u})|) :
    realizationProductSimplexHomeomorph p q (SSet.toTop.map (row p q i) w) =
      (StdSimplex.single i, SimplexCategory.toTopHomeo ⦋q⦌ w) := by
  rw [realizationProductSimplexHomeomorph_apply]
  apply Prod.ext
  · change SimplexCategory.toTopHomeo ⦋p⦌
      ((SSet.toTop.map (row p q i) ≫ SSet.toTop.map (fst Δ[p] Δ[q])) w) = _
    rw [← Functor.map_comp]
    change SimplexCategory.toTopHomeo ⦋p⦌
      (SSet.toTop.map (lift (SSet.stdSimplex.map (constantFace i)) (𝟙 _) ≫ fst _ _) w) = _
    rw [lift_fst, SimplexCategory.toTopHomeo_naturality_apply]
    exact StdSimplex.map_const _ i
  · change SimplexCategory.toTopHomeo ⦋q⦌
      ((SSet.toTop.map (row p q i) ≫ SSet.toTop.map (snd Δ[p] Δ[q])) w) = _
    rw [← Functor.map_comp]
    change SimplexCategory.toTopHomeo ⦋q⦌
      (SSet.toTop.map (lift (SSet.stdSimplex.map (constantFace i)) (𝟙 _) ≫ snd _ _) w) = _
    rw [lift_snd, CategoryTheory.Functor.map_id]
    rfl

/-- A whole row of the actual realized product parameter is the original affine simplex face. -/
theorem parameter_row (p q : ℕ) (i : Fin (p + 1)) (w : StdSimplex ℝ (Fin (q + 1))) :
    parameter.{u} p q (StdSimplex.single i, w) = StdSimplex.map (rowFace p q i).toOrderHom w := by
  have h := parameter_realization p q
    (SSet.toTop.map (row.{u} p q i) ((SimplexCategory.toTopHomeo ⦋q⦌).symm w))
  rw [homeomorph_row, Homeomorph.apply_symm_apply] at h
  change parameter p q (StdSimplex.single i, w) =
    SimplexCategory.toTopHomeo ⦋dimension p q⦌
      ((SSet.toTop.map (row p q i) ≫ SSet.toTop.map (embedding p q))
        ((SimplexCategory.toTopHomeo ⦋q⦌).symm w)) at h
  rw [← Functor.map_comp, row_embedding, SimplexCategory.toTopHomeo_naturality_apply,
    Homeomorph.apply_symm_apply] at h
  exact h

end Quillen.SimplexGrid
