/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MAllBoundaryNodes

/-! Actual product restrictions for the two coefficient edges and four projection edges. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Simplicial Topology
universe u
namespace Quillen.PerfectComplexes.BassMPrimitiveSupport
open Quillen.SimplexGrid

/-- The starting vertices 0 and 1 of the two consecutive coefficient normalization edges. -/
def coefficientEdgeStart : Fin 2 → Fin 3 := ![0, 1]
/-- The ending vertices 1 and 2 of the two consecutive coefficient normalization edges. -/
def coefficientEdgeEnd : Fin 2 → Fin 3 := ![1, 2]
/--
The one-simplex face selecting a consecutive coefficient normalization edge in the two-simplex.
-/
def coefficientEdgeFace (i : Fin 2) : ⦋1⦌ ⟶ ⦋2⦌ :=
  SimplexCategory.Hom.mk ⟨![coefficientEdgeStart i, coefficientEdgeEnd i],
    (by decide : ∀ i : Fin 2, Monotone
      (![coefficientEdgeStart i, coefficientEdgeEnd i] : Fin 2 → Fin 3)) i⟩

/-- The four grid vertices obtained by pairing coefficient edge `i` with projection edge `j`. -/
def middleEdgePairIndex (i : Fin 2) (j : Fin 4) : Fin 4 → Fin 15 :=
  ![index 2 4 (coefficientEdgeStart i, BassH1Support.edgeStart j),
    index 2 4 (coefficientEdgeStart i, BassH1Support.edgeEnd j),
    index 2 4 (coefficientEdgeEnd i, BassH1Support.edgeStart j),
    index 2 4 (coefficientEdgeEnd i, BassH1Support.edgeEnd j)]

/--
The three-simplex face of the 14-simplex spanned by coefficient edge `i` and projection edge
`j`.
-/
def middleEdgePairFace (i : Fin 2) (j : Fin 4) : ⦋3⦌ ⟶ ⦋14⦌ :=
  SimplexCategory.Hom.mk ⟨middleEdgePairIndex i j,
    (by decide : ∀ (i : Fin 2) (j : Fin 4), Monotone (middleEdgePairIndex i j)) i j⟩

/-- This exact four-vertex face respects both genuine edge coordinates. -/
theorem middleEdgePair_index (i : Fin 2) (j : Fin 4) (k l : Fin 2) :
    (middleEdgePairFace i j).toOrderHom (index 1 1 (k, l)) =
      index 2 4 ((coefficientEdgeFace i).toOrderHom k,
        (BassH1Support.edgeFace j).toOrderHom l) := by
  fin_cases k <;> fin_cases l <;> rfl

/-- The actual simplicial product of the two original edge inclusions. -/
def middleEdgeProduct (i : Fin 2) (j : Fin 4) : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ Δ[2] ⊗ Δ[4] :=
  lift (fst Δ[1] Δ[1] ≫ SSet.stdSimplex.map (coefficientEdgeFace i))
    (snd Δ[1] Δ[1] ≫ SSet.stdSimplex.map (BassH1Support.edgeFace j))

/-- Both ways into the grid simplex are the same simplicial map, at every simplex degree. -/
theorem middleEdgeProduct_embedding (i : Fin 2) (j : Fin 4) :
    middleEdgeProduct.{u} i j ≫ embedding 2 4 =
      embedding 1 1 ≫ SSet.stdSimplex.map (middleEdgePairFace i j) := by
  ext n z : 4
  apply SSet.stdSimplex.objEquiv.injective
  ext k
  exact congrArg Fin.val (middleEdgePair_index i j
    ((SSet.stdSimplex.objEquiv z.1).toOrderHom k)
    ((SSet.stdSimplex.objEquiv z.2).toOrderHom k)).symm

/-- The actual product homeomorphism retains both independently varying edge parameters. -/
theorem homeomorph_middleEdgeProduct (i : Fin 2) (j : Fin 4) (w : |(Δ[1] ⊗ Δ[1] : SSet.{u})|) :
    realizationProductSimplexHomeomorph 2 4 (SSet.toTop.map (middleEdgeProduct i j) w) =
      (StdSimplex.map (coefficientEdgeFace i).toOrderHom
        (realizationProductSimplexHomeomorph 1 1 w).1,
        StdSimplex.map (BassH1Support.edgeFace j).toOrderHom
          (realizationProductSimplexHomeomorph 1 1 w).2) := by
  rw [realizationProductSimplexHomeomorph_apply, realizationProductSimplexHomeomorph_apply]
  apply Prod.ext
  · change SimplexCategory.toTopHomeo ⦋2⦌
      ((SSet.toTop.map (middleEdgeProduct i j) ≫ SSet.toTop.map (fst Δ[2] Δ[4])) w) = _
    rw [← Functor.map_comp]
    change SimplexCategory.toTopHomeo ⦋2⦌
      (SSet.toTop.map (lift _ _ ≫ fst _ _) w) = _
    rw [lift_fst, Functor.map_comp]
    exact SimplexCategory.toTopHomeo_naturality_apply (coefficientEdgeFace i) _
  · change SimplexCategory.toTopHomeo ⦋4⦌
      ((SSet.toTop.map (middleEdgeProduct i j) ≫ SSet.toTop.map (snd Δ[2] Δ[4])) w) = _
    rw [← Functor.map_comp]
    change SimplexCategory.toTopHomeo ⦋4⦌
      (SSet.toTop.map (lift _ _ ≫ snd _ _) w) = _
    rw [lift_snd, Functor.map_comp]
    exact SimplexCategory.toTopHomeo_naturality_apply (BassH1Support.edgeFace j) _

/-- The genuine grid parameter on two original edges factors through this exact small face. -/
theorem parameter_middleEdgeProduct (i : Fin 2) (j : Fin 4)
    (z w : StdSimplex ℝ (Fin 2)) :
    parameter.{u} 2 4 (StdSimplex.map (coefficientEdgeFace i).toOrderHom z,
      StdSimplex.map (BassH1Support.edgeFace j).toOrderHom w) =
    StdSimplex.map (middleEdgePairFace i j).toOrderHom (parameter.{u} 1 1 (z, w)) := by
  have h := parameter_realization 2 4
    (SSet.toTop.map (middleEdgeProduct.{u} i j)
      ((realizationProductSimplexHomeomorph 1 1).symm (z, w)))
  rw [homeomorph_middleEdgeProduct, Homeomorph.apply_symm_apply] at h
  change parameter 2 4 (StdSimplex.map (coefficientEdgeFace i).toOrderHom z,
      StdSimplex.map (BassH1Support.edgeFace j).toOrderHom w) =
    SimplexCategory.toTopHomeo ⦋14⦌
      ((SSet.toTop.map (middleEdgeProduct i j) ≫ SSet.toTop.map (embedding 2 4))
        ((realizationProductSimplexHomeomorph 1 1).symm (z, w))) at h
  rw [← Functor.map_comp, middleEdgeProduct_embedding] at h
  have hc := congrArg
    (fun f : SSet.toTop.obj (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ SSet.toTop.obj Δ[14] ↦
      SimplexCategory.toTopHomeo ⦋14⦌
        (f ((realizationProductSimplexHomeomorph 1 1).symm (z, w))))
    (SSet.toTop.map_comp (embedding 1 1) (SSet.stdSimplex.map (middleEdgePairFace i j)))
  exact h.trans (hc.trans (SimplexCategory.toTopHomeo_naturality_apply (middleEdgePairFace i j) _))

end Quillen.PerfectComplexes.BassMPrimitiveSupport
