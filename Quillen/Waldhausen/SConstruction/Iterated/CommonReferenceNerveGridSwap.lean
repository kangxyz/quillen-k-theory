/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFiniteParameter
/-! Exact finite product interchange on full reference nerves, not on native evaluations. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Simplicial Topology
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.GridSwap

/-- Swap the two actual simplicial product factors. -/
def swap (p q : ℕ) : (Δ[p] ⊗ Δ[q] : SSet.{u}) ⟶ Δ[q] ⊗ Δ[p] :=
  lift (snd _ _) (fst _ _)

/-- The actual realization product comparison carries the swap to the ordinary pair swap. -/
theorem homeomorph_swap (p q : ℕ) (x : |(Δ[p] ⊗ Δ[q] : SSet.{u})|) :
    realizationProductSimplexHomeomorph q p (SSet.toTop.map (swap p q) x) =
      (realizationProductSimplexHomeomorph p q x).swap := by
  rw [realizationProductSimplexHomeomorph_apply, realizationProductSimplexHomeomorph_apply]
  apply Prod.ext
  · change SimplexCategory.toTopHomeo ⦋q⦌
      ((SSet.toTop.map (swap p q) ≫ SSet.toTop.map (fst Δ[q] Δ[p])) x) = _
    rw [← Functor.map_comp]
    change SimplexCategory.toTopHomeo ⦋q⦌
      (SSet.toTop.map (lift (snd _ _) (fst _ _) ≫ fst _ _) x) = _
    rw [lift_fst]
    rfl
  · change SimplexCategory.toTopHomeo ⦋p⦌
      ((SSet.toTop.map (swap p q) ≫ SSet.toTop.map (snd Δ[q] Δ[p])) x) = _
    rw [← Functor.map_comp]
    change SimplexCategory.toTopHomeo ⦋p⦌
      (SSet.toTop.map (lift (snd _ _) (fst _ _) ≫ snd _ _) x) = _
    rw [lift_snd]
    rfl

variable {V W : Model.{u}} (F : V ⟶ W) {p q : ℕ}
    (N : Fin (p + 1) → Fin (q + 1) → Node F)

/-- Flatten the original full dependent pair of indices in its specified order. -/
def nodes (i : Fin (SimplexGrid.dimension p q + 1)) : Node F :=
  N ((SimplexGrid.indexEquiv p q).symm i).1 ((SimplexGrid.indexEquiv p q).symm i).2

/-- Both simplicial product maps have literally the same full dependent node at every vertex. -/
theorem simplicial_swap :
    SimplexGrid.embedding p q ≫ simplexMap F (nodes F N) =
      swap p q ≫ SimplexGrid.embedding q p ≫ simplexMap F (nodes F (fun j i ↦ N i j)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · change Codiscrete.mk (nodes F N
      (SimplexGrid.index p q (z.1.down.toOrderHom i, z.2.down.toOrderHom i))) =
      Codiscrete.mk (nodes F (fun j i ↦ N i j)
        (SimplexGrid.index q p (z.2.down.toOrderHom i, z.1.down.toOrderHom i)))
    simp only [nodes, SimplexGrid.decode_index]
  · intro i j g
    apply Subsingleton.elim

/-- The two grid orders give the identical whole-nerve point at swapped independent parameters. -/
theorem parameter_swap (z : StdSimplex ℝ (Fin (p + 1)))
    (w : StdSimplex ℝ (Fin (q + 1))) :
    parameter F (nodes F N) (SimplexGrid.parameter.{u} p q (z, w)) =
      parameter F (nodes F (fun j i ↦ N i j)) (SimplexGrid.parameter.{u} q p (w, z)) := by
  let x := (realizationProductSimplexHomeomorph p q).symm (z, w)
  have hx : SSet.toTop.map (swap p q) x =
      (realizationProductSimplexHomeomorph q p).symm (w, z) := by
    apply (realizationProductSimplexHomeomorph q p).injective
    simp only [homeomorph_swap, x, Homeomorph.apply_symm_apply]
    rfl
  unfold parameter realizationSimplex SimplexGrid.parameter
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Homeomorph.symm_apply_apply]
  change (SSet.toTop.map (SimplexGrid.embedding p q) ≫
      SSet.toTop.map (simplexMap F (nodes F N))) x = _
  rw [← Functor.map_comp, simplicial_swap, Functor.map_comp, Functor.map_comp]
  change SSet.toTop.map (simplexMap F (nodes F (fun j i ↦ N i j)))
    (SSet.toTop.map (SimplexGrid.embedding q p) (SSet.toTop.map (swap p q) x)) = _
  rw [hx]
  rfl

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.GridSwap
