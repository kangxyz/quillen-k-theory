/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1OuterScalarWords

/-! Actual realization-product restrictions to pairs of the four original square-path edges. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Simplicial Topology
universe u
namespace Quillen.PerfectComplexes.BassH1Support
open Quillen.SimplexGrid

def edgeStart : Fin 4 → Fin 5 := ![0, 1, 0, 3]
def edgeEnd : Fin 4 → Fin 5 := ![1, 2, 3, 4]

def edgeFace (i : Fin 4) : ⦋1⦌ ⟶ ⦋4⦌ :=
  SimplexCategory.Hom.mk ⟨![edgeStart i, edgeEnd i],
    (by decide : ∀ i : Fin 4, Monotone (![edgeStart i, edgeEnd i] : Fin 2 → Fin 5)) i⟩

def edgePairIndex (i j : Fin 4) : Fin 4 → Fin 25 :=
  ![index 4 4 (edgeStart i, edgeStart j), index 4 4 (edgeStart i, edgeEnd j),
    index 4 4 (edgeEnd i, edgeStart j), index 4 4 (edgeEnd i, edgeEnd j)]

def edgePairFace (i j : Fin 4) : ⦋3⦌ ⟶ ⦋24⦌ :=
  SimplexCategory.Hom.mk ⟨edgePairIndex i j,
    (by decide : ∀ i j : Fin 4, Monotone (edgePairIndex i j)) i j⟩

/-- This exact four-vertex face respects both genuine edge coordinates. -/
theorem edgePair_index (i j : Fin 4) (k l : Fin 2) :
    (edgePairFace i j).toOrderHom (index 1 1 (k, l)) =
      index 4 4 ((edgeFace i).toOrderHom k, (edgeFace j).toOrderHom l) := by
  fin_cases k <;> fin_cases l <;> rfl

/-- The actual simplicial product of the two original edge inclusions. -/
def edgeProduct (i j : Fin 4) : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ Δ[4] ⊗ Δ[4] :=
  lift (fst Δ[1] Δ[1] ≫ SSet.stdSimplex.map (edgeFace i))
    (snd Δ[1] Δ[1] ≫ SSet.stdSimplex.map (edgeFace j))

/-- Both ways into the grid simplex are the same simplicial map, at every simplex degree. -/
theorem edgeProduct_embedding (i j : Fin 4) :
    edgeProduct.{u} i j ≫ embedding 4 4 =
      embedding 1 1 ≫ SSet.stdSimplex.map (edgePairFace i j) := by
  ext n z : 4
  apply SSet.stdSimplex.objEquiv.injective
  ext k
  exact congrArg Fin.val (edgePair_index i j
    ((SSet.stdSimplex.objEquiv z.1).toOrderHom k)
    ((SSet.stdSimplex.objEquiv z.2).toOrderHom k)).symm

/-- The actual product homeomorphism retains both independently varying edge parameters. -/
theorem homeomorph_edgeProduct (i j : Fin 4) (w : |(Δ[1] ⊗ Δ[1] : SSet.{u})|) :
    realizationProductSimplexHomeomorph 4 4 (SSet.toTop.map (edgeProduct i j) w) =
      (StdSimplex.map (edgeFace i).toOrderHom (realizationProductSimplexHomeomorph 1 1 w).1,
        StdSimplex.map (edgeFace j).toOrderHom (realizationProductSimplexHomeomorph 1 1 w).2) := by
  rw [realizationProductSimplexHomeomorph_apply, realizationProductSimplexHomeomorph_apply]
  apply Prod.ext
  · change SimplexCategory.toTopHomeo ⦋4⦌
      ((SSet.toTop.map (edgeProduct i j) ≫ SSet.toTop.map (fst Δ[4] Δ[4])) w) = _
    rw [← Functor.map_comp]
    change SimplexCategory.toTopHomeo ⦋4⦌
      (SSet.toTop.map (lift _ _ ≫ fst _ _) w) = _
    rw [lift_fst, Functor.map_comp]
    exact SimplexCategory.toTopHomeo_naturality_apply (edgeFace i) _
  · change SimplexCategory.toTopHomeo ⦋4⦌
      ((SSet.toTop.map (edgeProduct i j) ≫ SSet.toTop.map (snd Δ[4] Δ[4])) w) = _
    rw [← Functor.map_comp]
    change SimplexCategory.toTopHomeo ⦋4⦌
      (SSet.toTop.map (lift _ _ ≫ snd _ _) w) = _
    rw [lift_snd, Functor.map_comp]
    exact SimplexCategory.toTopHomeo_naturality_apply (edgeFace j) _

/-- The genuine grid parameter on two original edges factors through this exact small face. -/
theorem parameter_edgeProduct (i j : Fin 4)
    (z w : StdSimplex ℝ (Fin 2)) :
    parameter.{u} 4 4 (StdSimplex.map (edgeFace i).toOrderHom z,
      StdSimplex.map (edgeFace j).toOrderHom w) =
    StdSimplex.map (edgePairFace i j).toOrderHom (parameter.{u} 1 1 (z, w)) := by
  have h := parameter_realization 4 4
    (SSet.toTop.map (edgeProduct.{u} i j)
      ((realizationProductSimplexHomeomorph 1 1).symm (z, w)))
  rw [homeomorph_edgeProduct, Homeomorph.apply_symm_apply] at h
  change parameter 4 4 (StdSimplex.map (edgeFace i).toOrderHom z,
      StdSimplex.map (edgeFace j).toOrderHom w) =
    SimplexCategory.toTopHomeo ⦋24⦌
      ((SSet.toTop.map (edgeProduct i j) ≫ SSet.toTop.map (embedding 4 4))
        ((realizationProductSimplexHomeomorph 1 1).symm (z, w))) at h
  rw [← Functor.map_comp, edgeProduct_embedding] at h
  have hc := congrArg
    (fun f : SSet.toTop.obj (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ SSet.toTop.obj Δ[24] ↦
      SimplexCategory.toTopHomeo ⦋24⦌
        (f ((realizationProductSimplexHomeomorph 1 1).symm (z, w))))
    (SSet.toTop.map_comp (embedding 1 1) (SSet.stdSimplex.map (edgePairFace i j)))
  exact h.trans (hc.trans (SimplexCategory.toTopHomeo_naturality_apply (edgePairFace i j) _))

end Quillen.PerfectComplexes.BassH1Support
