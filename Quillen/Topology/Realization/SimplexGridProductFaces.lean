/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.SimplexProductParameter

/-! Naturality of the actual realization-product parameter on compatible product faces.
The grid inclusion is an explicitly supplied monotone map preserving every ordered pair;
no coordinate-product formula for barycentric weights is assumed. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Simplicial Topology
universe u
namespace Quillen.SimplexGrid
variable {p q p' q' : ℕ}

/-- The actual simplicial product of two prescribed simplex maps. -/
def productMap (α : ⦋p⦌ ⟶ ⦋p'⦌) (β : ⦋q⦌ ⟶ ⦋q'⦌) :
    (Δ[p] ⊗ Δ[q] : SSet.{u}) ⟶ Δ[p'] ⊗ Δ[q'] :=
  lift (fst Δ[p] Δ[q] ≫ SSet.stdSimplex.map α)
    (snd Δ[p] Δ[q] ≫ SSet.stdSimplex.map β)

/-- Pairwise compatibility identifies the two complete simplicial grid maps. -/
theorem productMap_embedding (α : ⦋p⦌ ⟶ ⦋p'⦌) (β : ⦋q⦌ ⟶ ⦋q'⦌)
    (γ : ⦋dimension p q⦌ ⟶ ⦋dimension p' q'⦌)
    (hγ : ∀ i j, γ.toOrderHom (index p q (i, j)) =
      index p' q' (α.toOrderHom i, β.toOrderHom j)) :
    productMap.{u} α β ≫ embedding p' q' = embedding p q ≫ SSet.stdSimplex.map γ := by
  ext n z : 4
  apply SSet.stdSimplex.objEquiv.injective
  ext k
  exact congrArg Fin.val (hγ
    ((SSet.stdSimplex.objEquiv z.1).toOrderHom k)
    ((SSet.stdSimplex.objEquiv z.2).toOrderHom k)).symm

/-- The genuine product homeomorphism preserves both independently varying face coordinates. -/
theorem homeomorph_productMap (α : ⦋p⦌ ⟶ ⦋p'⦌) (β : ⦋q⦌ ⟶ ⦋q'⦌)
    (w : |(Δ[p] ⊗ Δ[q] : SSet.{u})|) :
    realizationProductSimplexHomeomorph p' q' (SSet.toTop.map (productMap α β) w) =
      (StdSimplex.map α.toOrderHom (realizationProductSimplexHomeomorph p q w).1,
        StdSimplex.map β.toOrderHom (realizationProductSimplexHomeomorph p q w).2) := by
  rw [realizationProductSimplexHomeomorph_apply, realizationProductSimplexHomeomorph_apply]
  apply Prod.ext
  · change SimplexCategory.toTopHomeo ⦋p'⦌
      ((SSet.toTop.map (productMap α β) ≫ SSet.toTop.map (fst Δ[p'] Δ[q'])) w) = _
    rw [← Functor.map_comp]
    change SimplexCategory.toTopHomeo ⦋p'⦌
      (SSet.toTop.map (lift _ _ ≫ fst _ _) w) = _
    rw [lift_fst, Functor.map_comp]
    exact SimplexCategory.toTopHomeo_naturality_apply α _
  · change SimplexCategory.toTopHomeo ⦋q'⦌
      ((SSet.toTop.map (productMap α β) ≫ SSet.toTop.map (snd Δ[p'] Δ[q'])) w) = _
    rw [← Functor.map_comp]
    change SimplexCategory.toTopHomeo ⦋q'⦌
      (SSet.toTop.map (lift _ _ ≫ snd _ _) w) = _
    rw [lift_snd, Functor.map_comp]
    exact SimplexCategory.toTopHomeo_naturality_apply β _

/-- The realized grid parameter restricts to the specified product face at every point. -/
theorem parameter_productMap (α : ⦋p⦌ ⟶ ⦋p'⦌) (β : ⦋q⦌ ⟶ ⦋q'⦌)
    (γ : ⦋dimension p q⦌ ⟶ ⦋dimension p' q'⦌)
    (hγ : ∀ i j, γ.toOrderHom (index p q (i, j)) =
      index p' q' (α.toOrderHom i, β.toOrderHom j))
    (z : StdSimplex ℝ (Fin (p + 1))) (w : StdSimplex ℝ (Fin (q + 1))) :
    parameter.{u} p' q' (StdSimplex.map α.toOrderHom z, StdSimplex.map β.toOrderHom w) =
      StdSimplex.map γ.toOrderHom (parameter.{u} p q (z, w)) := by
  have h := parameter_realization p' q'
    (SSet.toTop.map (productMap.{u} α β)
      ((realizationProductSimplexHomeomorph p q).symm (z, w)))
  rw [homeomorph_productMap, Homeomorph.apply_symm_apply] at h
  change parameter p' q' (StdSimplex.map α.toOrderHom z, StdSimplex.map β.toOrderHom w) =
    SimplexCategory.toTopHomeo ⦋dimension p' q'⦌
      ((SSet.toTop.map (productMap α β) ≫ SSet.toTop.map (embedding p' q'))
        ((realizationProductSimplexHomeomorph p q).symm (z, w))) at h
  rw [← Functor.map_comp, productMap_embedding α β γ hγ] at h
  have hc := congrArg
    (fun f : SSet.toTop.obj (Δ[p] ⊗ Δ[q] : SSet.{u}) ⟶
        SSet.toTop.obj Δ[dimension p' q'] ↦
      SimplexCategory.toTopHomeo ⦋dimension p' q'⦌
        (f ((realizationProductSimplexHomeomorph p q).symm (z, w))))
    (SSet.toTop.map_comp (embedding p q) (SSet.stdSimplex.map γ))
  exact h.trans (hc.trans (SimplexCategory.toTopHomeo_naturality_apply γ _))

end Quillen.SimplexGrid
