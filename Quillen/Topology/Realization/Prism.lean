/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Realization.PrismCoordinates
public import Quillen.Topology.Realization.Cylinder
public import Quillen.Topology.Realization.Connectivity
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne

/-!
# Cells of the realized standard prism

This file constructs the canonical continuous cylinder comparison and the
realized maximal prism cells. The cells cover the entire realization, and
adjacent cells agree on their common simplicial face.
-/
@[expose] public section

noncomputable section

open Convexity CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial Topology unitInterval

universe u

namespace Quillen

/-- The canonical continuous map from the realized simplicial cylinder to
the topological cylinder. -/
def realizationCylinderComparison (X : SSet.{u}) : |X ⊗ Δ[1]| ⟶ |X| ⊗ TopCat.I :=
  lift (SSet.toTop.map (fst X Δ[1]))
    (SSet.toTop.map (snd X Δ[1]) ≫ SSet.stdSimplex.toTopObjIsoI.hom)

@[simp]
theorem realizationCylinderComparison_fst (X : SSet.{u}) :
    realizationCylinderComparison X ≫ fst _ _ = SSet.toTop.map (fst X Δ[1]) := by
  simp [realizationCylinderComparison]

@[simp]
theorem realizationCylinderComparison_snd (X : SSet.{u}) :
    realizationCylinderComparison X ≫ snd _ _ =
      SSet.toTop.map (snd X Δ[1]) ≫ SSet.stdSimplex.toTopObjIsoI.hom := by
  simp [realizationCylinderComparison]

/-- Cylinder comparison is natural in the simplicial set. -/
theorem realizationCylinderComparison_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.toTop.map (f ▷ Δ[1]) ≫ realizationCylinderComparison Y =
      realizationCylinderComparison X ≫ (SSet.toTop.map f ▷ TopCat.I) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [realizationCylinderComparison, ← Category.assoc, ← Functor.map_comp]

/-- A maximal cell in the standard simplicial prism, after geometric realization. -/
def realizationPrismCell {n : ℕ} (i : Fin (n + 1)) :
    |(Δ[n + 1] : SSet.{u})| ⟶ |(Δ[n] ⊗ Δ[1] : SSet.{u})| :=
  SSet.toTop.map (SSet.yonedaEquiv.symm
    (SSet.prodStdSimplex₁.nonDegenerateEquiv i).val)

/-- The prism comparison in ordinary barycentric simplex and interval coordinates. -/
def realizationPrismCoordinates (n : ℕ) :
    C(|(Δ[n] ⊗ Δ[1] : SSet.{u})|, Convexity.StdSimplex ℝ (Fin (n + 1)) × unitInterval) where
  toFun x := (SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map (fst Δ[n] Δ[1]) x),
    Convexity.StdSimplex.homeomorphI
      (SimplexCategory.toTopHomeo ⦋1⦌ (SSet.toTop.map (snd Δ[n] Δ[1]) x)))
  continuous_toFun := by fun_prop

@[simp]
theorem realizationPrismCell_fst {n : ℕ} (i : Fin (n + 1)) :
    realizationPrismCell.{u} i ≫ SSet.toTop.map (fst Δ[n] Δ[1]) =
      SSet.toTop.map (SSet.stdSimplex.σ i) := by
  unfold realizationPrismCell
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp]
  rfl

@[simp]
theorem realizationPrismCell_snd {n : ℕ} (i : Fin (n + 1)) :
    realizationPrismCell.{u} i ≫ SSet.toTop.map (snd Δ[n] Δ[1]) =
      SSet.toTop.map (SSet.stdSimplex.map
        (SSet.stdSimplex.objEquiv.{u} (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc))) := by
  unfold realizationPrismCell
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp]
  rfl

/-- The first prism coordinate collapses the two copies of the split vertex. -/
theorem realizationPrismCoordinates_cell_fst {n : ℕ} (i : Fin (n + 1))
    (v : StdSimplex ℝ (Fin (n + 2))) :
    (realizationPrismCoordinates n (realizationPrismCell.{u} i
      ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm v))).1 = v.map i.predAbove := by
  change SimplexCategory.toTopHomeo ⦋n⦌ ((realizationPrismCell i ≫
    SSet.toTop.map (fst Δ[n] Δ[1])) _) = _
  rw [realizationPrismCell_fst]
  change SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map
    (SSet.stdSimplex.map (SimplexCategory.σ i)) _) = _
  rw [SimplexCategory.toTopHomeo_naturality_apply, Homeomorph.apply_symm_apply]
  rfl

/-- The second prism coordinate is the total mass above the cut. -/
theorem realizationPrismCoordinates_cell_snd {n : ℕ} (i : Fin (n + 1))
    (v : StdSimplex ℝ (Fin (n + 2))) :
    ((realizationPrismCoordinates n (realizationPrismCell.{u} i
      ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm v))).2 : ℝ) = prismHeight i v := by
  change (StdSimplex.homeomorphI (SimplexCategory.toTopHomeo ⦋1⦌
    ((realizationPrismCell i ≫ SSet.toTop.map (snd Δ[n] Δ[1])) _)) : ℝ) = _
  rw [realizationPrismCell_snd, SimplexCategory.toTopHomeo_naturality_apply,
    Homeomorph.apply_symm_apply]
  rw [StdSimplex.homeomorphI_apply_coe]
  change (v.map (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc)).weights 1 = _
  classical
  rw [StdSimplex.weights_map, Finsupp.mapDomain_fintype]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, prismHeight]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finsupp.single_apply]
  congr 1
  rw [SSet.stdSimplex.objMk₁_apply_eq_one_iff]
  simp only [Fin.castSucc_le_castSucc_iff]
  rfl

/-- Every simplex in a standard prism is a face or degeneracy of a maximal prism cell. -/
theorem prism_simplex_factors {n : ℕ} {m : SimplexCategoryᵒᵖ}
    (s : (Δ[n] ⊗ Δ[1] : SSet.{u}).obj m) :
    ∃ (i : Fin (n + 1)) (f : m.unop ⟶ ⦋n + 1⦌),
      (Δ[n] ⊗ Δ[1]).map f.op (SSet.prodStdSimplex₁.nonDegenerateEquiv i).val = s := by
  have hs : s ∈ (SSet.prodStdSimplex₁.filtration.{u} (Fin.last n)).obj m := by
    rw [SSet.prodStdSimplex₁.filtration_last]
    trivial
  simp only [SSet.prodStdSimplex₁.filtration, Subfunctor.iSup_obj, Set.mem_iUnion] at hs
  obtain ⟨i, hi⟩ := hs
  obtain ⟨f, hf⟩ := (SSet.Subcomplex.mem_ofSimplex_obj_iff _ _).mp hi
  exact ⟨i.val, f, hf⟩

/-- The finitely many maximal realized cells cover the standard prism. -/
theorem realizationPrismCell_jointly_surjective {n : ℕ}
    (x : |(Δ[n] ⊗ Δ[1] : SSet.{u})|) :
    ∃ (i : Fin (n + 1)) (t : |(Δ[n + 1] : SSet.{u})|), realizationPrismCell i t = x := by
  obtain ⟨m, f, t, rfl⟩ := realization_exists_simplex x
  obtain ⟨i, g, hg⟩ := prism_simplex_factors (SSet.yonedaEquiv f)
  refine ⟨i, SSet.toTop.map (SSet.stdSimplex.map g) t, ?_⟩
  change (SSet.toTop.map (SSet.stdSimplex.map g) ≫
    SSet.toTop.map (SSet.yonedaEquiv.symm _)) t = _
  rw [← Functor.map_comp]
  have heq : SSet.stdSimplex.map g ≫ SSet.yonedaEquiv.symm
      (SSet.prodStdSimplex₁.nonDegenerateEquiv i).val = f := by
    apply SSet.yonedaEquiv.injective
    exact hg
  rw [heq]

/-- A finite-dimensional barycentric standard simplex is compact. -/
instance finiteStdSimplex_compactSpace {M : Type*} [Finite M] :
    CompactSpace (StdSimplex ℝ M) := by
  apply isCompact_univ_iff.mp
  have h := (StdSimplex.isClosedEmbedding_toFun_comp_weights ℝ M).isCompact_preimage
    (isCompact_univ_pi (fun _ : M ↦ isCompact_Icc (a := (0 : ℝ)) (b := 1)))
  convert h using 1
  ext x
  simp only [Set.mem_univ, Set.mem_preimage, Set.mem_pi, Set.mem_Icc, true_iff,
    Set.mem_univ, forall_true_left]
  exact fun i ↦ ⟨x.weights_nonneg i, x.weights_apply_le_one i⟩

/-- Realizations of representable simplicial sets are compact. -/
instance realizationStandardSimplex_compactSpace (n : SimplexCategory) :
    CompactSpace |SSet.stdSimplex.{u}.obj n| :=
  (SimplexCategory.toTopHomeo n).symm.compactSpace

/-- The realized standard prism is compact, as a finite union of compact maximal cells. -/
instance realizationPrism_compactSpace (n : ℕ) :
    CompactSpace |(Δ[n] ⊗ Δ[1] : SSet.{u})| := by
  let f : (Σ _ : Fin (n + 1), |(Δ[n + 1] : SSet.{u})|) →
      |(Δ[n] ⊗ Δ[1] : SSet.{u})| := fun z ↦ realizationPrismCell z.1 z.2
  have hf : Continuous f := by
    apply continuous_sigma
    intro i
    exact (realizationPrismCell i).hom.continuous
  exact Function.Surjective.compactSpace hf (fun x ↦ by
    obtain ⟨i, t, ht⟩ := realizationPrismCell_jointly_surjective x
    exact ⟨⟨i, t⟩, ht⟩)

/-- Adjacent realized prism cells agree on their shared codimension-one face. -/
theorem realizationPrismCell_adjacent_face {n : ℕ} (i : Fin n) :
    SSet.toTop.map (SSet.stdSimplex.δ i.castSucc.succ) ≫
        realizationPrismCell.{u} i.castSucc =
      SSet.toTop.map (SSet.stdSimplex.δ i.succ.castSucc) ≫
        realizationPrismCell.{u} i.succ := by
  unfold realizationPrismCell
  rw [← Functor.map_comp, ← Functor.map_comp,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
    SSet.prodStdSimplex₁.δ_succ_nonDegenerateEquiv,
    SSet.prodStdSimplex₁.δ_castSucc_nonDegenerateEquiv, Fin.succ_castSucc]

end Quillen
