/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.TheoremB.ReplacementVertex
public import Quillen.CategoryTheory.TheoremB.TotalProjection

/-! The actual first base-skeleton of a simplicial replacement is the
coproduct of its diagram values, with the true realization topology. -/
@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.TheoremA
variable {D : Type u} [SmallCategory D]

/-- A base chain belonging to the vertex skeleton is constant. -/
theorem nerve_skeleton_one_constant {p : SimplexCategoryᵒᵖ}
    (s : (nerve D).obj p) (hs : s ∈ ((nerve D).skeleton 1).obj p) :
    s = (Functor.const (Fin (p.unop.len + 1))).obj (s.obj 0) := by
  simp only [SSet.skeleton, OrderHom.coe_mk, Subfunctor.iSup_obj,
    Set.iUnion_coe_set, Set.mem_iUnion, exists_prop] at hs
  obtain ⟨⟨n, hn⟩, x, hx, ⟨f⟩, rfl⟩ := hs
  have hn0 : n = 0 := by omega
  subst n
  obtain ⟨d, rfl⟩ := ComposableArrows.mk₀_surjective x
  rfl

/-- Every constant chain belongs to the actual vertex skeleton. -/
theorem nerve_constant_mem_skeleton_one (d : D) (p : SimplexCategoryᵒᵖ) :
    (Functor.const (Fin (p.unop.len + 1))).obj d ∈ ((nerve D).skeleton 1).obj p := by
  let α : op ⦋0⦌ ⟶ p := (SimplexCategory.const p.unop ⦋0⦌ 0).op
  have h := ((nerve D).skeleton 1).map α
    ((nerve D).mem_skeleton (nerveVertex d) (by omega))
  exact h

variable (H : D ⥤ SSet.{u})

/-- The vertex coproduct includes canonically into the first diagonal base-skeleton. -/
def vertexCoproductToStageOne : simplicialSigma (fun d : D ↦ H.obj d) ⟶
    diagonalSSet ((replacementSkeleton H).obj 1) where
  app p := ↾fun x ↦ ⟨⟨(Functor.const (Fin (p.unop.len + 1))).obj x.1,
    nerve_constant_mem_skeleton_one x.1 p⟩, x.2⟩
  naturality p q α := by
    ext x : 3
    dsimp [diagonalSSet, replacementSkeleton, replacementRestriction,
      replacementRestrictionRowMap, firstVertexEdge, simplicialSigma]
    simp only [H.map_id]
    rfl

instance vertexCoproductToStageOne_isIso : IsIso (vertexCoproductToStageOne H) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro p
  apply (isIso_iff_bijective _).2
  constructor
  · intro x y hxy
    obtain ⟨hb, hf⟩ := Sigma.ext_iff.mp hxy
    have hbase : x.1 = y.1 := congrArg (fun z ↦ z.1.obj 0) hb
    exact Sigma.ext hbase hf
  · intro z
    refine ⟨⟨z.1.1.obj 0, z.2⟩, ?_⟩
    apply Sigma.ext
    · exact Subtype.ext (nerve_skeleton_one_constant z.1.1 z.1.2).symm
    · rfl

/-- Exact simplicial coproduct coordinates for the first base-skeleton. -/
def replacementStageOneIso :
    simplicialSigma (fun d : D ↦ H.obj d) ≅ diagonalSSet ((replacementSkeleton H).obj 1) :=
  asIso (vertexCoproductToStageOne H)

/-- The first stage after realization is the genuine topological coproduct
of the diagram's realized values. -/
def realizedReplacementStageOneHomeomorph :
    (Σ d : D, |H.obj d|) ≃ₜ (realizedReplacementSkeleton H).obj 1 :=
  (TopCat.homeoOfIso (realizationSigmaIso (fun d : D ↦ H.obj d))).symm.trans
    (TopCat.homeoOfIso (SSet.toTop.mapIso (replacementStageOneIso H)))

/-- The first-stage coproduct inclusion followed by the exhaustive cocone
is precisely the previously constructed vertex inclusion. -/
theorem vertexCoproductToStageOne_ι (d : D) :
    simplicialSigmaι (fun d : D ↦ H.obj d) d ≫ vertexCoproductToStageOne H ≫
      diagonalMap (replacementRestrictionι H ((nerve D).skeleton 1)) =
        replacementVertexInclusion H d := rfl

/-- The homeomorphism includes each value by its actual realized simplicial map. -/
theorem realizedReplacementStageOneHomeomorph_apply (d : D) (x : |H.obj d|) :
    realizedReplacementStageOneHomeomorph H ⟨d, x⟩ =
      SSet.toTop.map (simplicialSigmaι (fun d : D ↦ H.obj d) d ≫
        vertexCoproductToStageOne H) x := by
  change SSet.toTop.map (vertexCoproductToStageOne H)
    ((realizationSigmaIso (fun d : D ↦ H.obj d)).inv ⟨d, x⟩) = _
  rw [realizationSigmaIso_inv_apply]
  rw [Functor.map_comp]
  rfl

/-- Coefficient maps retain the discrete object coordinate in stage one. -/
theorem realizedReplacementStageOneHomeomorph_naturality
    {H K : D ⥤ SSet.{u}} (η : H ⟶ K) (d : D) (x : |H.obj d|) :
    (realizedReplacementSkeletonMap η).app 1
      (realizedReplacementStageOneHomeomorph H ⟨d, x⟩) =
      realizedReplacementStageOneHomeomorph K ⟨d, SSet.toTop.map (η.app d) x⟩ := by
  rw [realizedReplacementStageOneHomeomorph_apply, realizedReplacementStageOneHomeomorph_apply]
  change (SSet.toTop.map (simplicialSigmaι (fun d : D ↦ H.obj d) d ≫
      vertexCoproductToStageOne H) ≫
    SSet.toTop.map (diagonalMap ((replacementSkeletonMap η).app 1))) x =
    (SSet.toTop.map (η.app d) ≫
      SSet.toTop.map (simplicialSigmaι (fun d : D ↦ K.obj d) d ≫
        vertexCoproductToStageOne K)) x
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- Coproduct coordinates retain the exact canonical vertex inclusion into
full realization. -/
theorem realizedReplacementStageOneHomeomorph_colimit (d : D) (x : |H.obj d|) :
    (realizedReplacementSkeletonCocone H).ι.app 1
      (realizedReplacementStageOneHomeomorph H ⟨d, x⟩) =
        SSet.toTop.map (replacementVertexInclusion H d) x := by
  rw [realizedReplacementStageOneHomeomorph_apply]
  change (SSet.toTop.map (simplicialSigmaι (fun d : D ↦ H.obj d) d ≫
    vertexCoproductToStageOne H) ≫
      SSet.toTop.map (diagonalMap (replacementRestrictionι H ((nerve D).skeleton 1)))) x = _
  rw [← Functor.map_comp, Category.assoc, vertexCoproductToStageOne_ι]
  rfl

/-- Every replacement vertex projects to its indexing vertex. -/
theorem replacementVertex_base (d : D) (x : |H.obj d|) :
    SSet.toTop.map (replacementBaseMap H)
      (SSet.toTop.map (replacementVertexInclusion H d) x) = classifyingSpacePoint d := by
  change (SSet.toTop.map (replacementVertexInclusion H d) ≫
    SSet.toTop.map (replacementBaseMap H)) x = _
  rw [← Functor.map_comp]
  exact realization_const (nerveVertex d) x

end Quillen.TheoremA
