/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexReverseMixedWeakProduct
public import Quillen.Topology.Realization.JointSimplexParameter
public import Quillen.Topology.Realization.SimplexGridColumn
/-! # Exact realization of source-isomorphism and weak simplex products

The source isomorphism family runs before the weak family. The original realization-product
parameter still has weak coordinate first; the actual simplicial symmetry and natural product
comparison prove the transposition, including all original level-zero loop inputs.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Opposite MonoidalCategory
  CartesianMonoidalCategory Convexity
open scoped Simplicial Topology
universe u
namespace Quillen.Waldhausen.IteratedS.ReverseMixedWeakProduct
variable {V W T : Model.{u}} {p q : ℕ}
variable (S : ModelSimplex W T p)
  (G₀ : V ⟶ W) (G : Fin (q + 1) → (V ⟶ W))
  (σ : ∀ i, G₀.functor ≅ (G i).functor)

/-- The genuine simplicial symmetry respects the original product comparison. -/
private theorem realization_swap_hom (p q : ℕ) :
    SSet.toTop.map (lift (snd Δ[q] Δ[p]) (fst Δ[q] Δ[p])) ≫
      (realizationProductSimplexIso Δ[p] q).hom =
    (realizationProductSimplexIso Δ[q] p).hom ≫
      lift (snd |(Δ[q] : SSet.{u})| |(Δ[p] : SSet.{u})|)
        (fst |(Δ[q] : SSet.{u})| |(Δ[p] : SSet.{u})|) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [realizationProductSimplexIso_hom, ← Functor.map_comp]

/-- The inverse product comparisons preserve the two independent coordinates under symmetry. -/
private theorem realization_swap_inv (p q : ℕ)
    (z : |(Δ[p] : SSet.{u})|) (w : |(Δ[q] : SSet.{u})|) :
    SSet.toTop.map (lift (snd Δ[q] Δ[p]) (fst Δ[q] Δ[p]))
      ((realizationProductSimplexIso Δ[q] p).inv (w, z)) =
    (realizationProductSimplexIso Δ[p] q).inv (z, w) := by
  apply (TopCat.homeoOfIso (realizationProductSimplexIso Δ[p] q)).injective
  have h := ConcreteCategory.congr_hom (realization_swap_hom p q)
    ((realizationProductSimplexIso Δ[q] p).inv (w, z))
  change (realizationProductSimplexIso Δ[p] q).hom _ =
    (realizationProductSimplexIso Δ[p] q).hom
      ((realizationProductSimplexIso Δ[p] q).inv (z, w))
  simp only [TopCat.comp_app, Iso.inv_hom_id_apply] at h ⊢
  convert h using 1
  rfl

/-- The swapped embedding has exactly the original weak-first grid parameter. -/
theorem realization_embedding (z : |(Δ[p] : SSet.{u})|)
    (w : |(Δ[q] : SSet.{u})|) :
    SSet.toTop.map (embedding p q)
      ((realizationProductSimplexIso Δ[q] p).inv (w, z)) =
    SSet.toTop.map (SimplexGrid.embedding p q)
      ((realizationProductSimplexIso Δ[p] q).inv (z, w)) := by
  simp only [embedding, Functor.map_comp, TopCat.comp_app, realization_swap_inv]

/-- The actual realization of the common grid family is literal composition of the two whole
original realized families, with their parameters independent. -/
theorem realization_comp (r : ℕ) (x : stageSpace r V)
    (z : |(Δ[p] : SSet.{u})|) (w : |(Δ[q] : SSet.{u})|) :
    stageSimplexRealization r (simplex S G₀ G σ)
      (x, SSet.toTop.map (SimplexGrid.embedding p q)
        ((realizationProductSimplexIso Δ[p] q).inv (z, w))) =
      stageSimplexRealization r S
        (stageSimplexRealization r (ModelSimplex.ofIsos G₀ G σ) (x, w), z) := by
  let X := (stages r).obj V
  let Y := (stages r).obj W
  let H := stageTransformationSimplex r (ModelSimplex.ofIsos G₀ G σ)
  let K := stageTransformationSimplex r S
  let D := stageTransformationSimplex r (simplex S G₀ G σ)
  rw [← realization_embedding z w]
  let ξ := (realizationProductSimplexIso (X ⊗ Δ[q]) p).inv
    ((realizationProductSimplexIso X q).inv (x, w), z)
  have hS := ConcreteCategory.congr_hom (realizationProductSimplexIso_inv_whisker H p)
    ((realizationProductSimplexIso X q).inv (x, w), z)
  change SSet.toTop.map (H ▷ Δ[p]) ξ =
    (realizationProductSimplexIso Y p).inv
      (SSet.toTop.map H ((realizationProductSimplexIso X q).inv (x, w)), z) at hS
  change SSet.toTop.map D ((realizationProductSimplexIso X (SimplexGrid.dimension p q)).inv
    (x, SSet.toTop.map (embedding p q)
      ((realizationProductSimplexIso Δ[q] p).inv (w, z)))) =
    SSet.toTop.map K ((realizationProductSimplexIso Y p).inv
      (SSet.toTop.map H ((realizationProductSimplexIso X q).inv (x, w)), z))
  rw [← hS, ← realization_joint_parameter_apply X (embedding p q) x w z]
  change (SSet.toTop.map ((α_ X Δ[q] Δ[p]).hom ≫ X ◁ embedding p q) ≫
    SSet.toTop.map D) ξ =
    (SSet.toTop.map (H ▷ Δ[p]) ≫ SSet.toTop.map K) ξ
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun h ↦ SSet.toTop.map h ξ)
    ((Category.assoc _ _ _).trans (stage_transformation_comp S G₀ G σ r))

/-- The exact barycentric product parameter reproduces the whole original stage composition. -/
theorem barycentric_comp (r : ℕ) (x : stageSpace r V)
    (z : StdSimplex ℝ (Fin (p + 1))) (w : StdSimplex ℝ (Fin (q + 1))) :
    stageSimplexBarycentric (simplex S G₀ G σ) r
      (SimplexGrid.parameter.{u} p q (z, w), x) =
      stageSimplexBarycentric S r
        (z, stageSimplexBarycentric (ModelSimplex.ofIsos G₀ G σ) r (w, x)) := by
  change stageSimplexRealization r (simplex S G₀ G σ)
    (x, (SimplexCategory.toTopHomeo ⦋SimplexGrid.dimension p q⦌).symm
      (SimplexGrid.parameter p q (z, w))) = _
  unfold SimplexGrid.parameter
  simp only [ContinuousMap.coe_mk, Homeomorph.symm_apply_apply]
  exact realization_comp S G₀ G σ r x
    ((SimplexCategory.toTopHomeo ⦋p⦌).symm z)
    ((SimplexCategory.toTopHomeo ⦋q⦌).symm w)

/-- Composition of both independently varying whole families at every original prespectrum level,
including the original loop input at level zero. -/
theorem prespectrum_comp (n : ℕ) (x : (prespectrum V).space n)
    (z : StdSimplex ℝ (Fin (p + 1))) (w : StdSimplex ℝ (Fin (q + 1))) :
    prespectrumSimplexFamily (simplex S G₀ G σ) n
      (SimplexGrid.parameter.{u} p q (z, w), x) =
      prespectrumSimplexFamily S n
        (z, prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G σ) n (w, x)) := by
  cases n with
  | zero =>
    change Path (stagePoint 0 V) (stagePoint 0 V) at x
    apply Path.ext
    funext t
    exact barycentric_comp S G₀ G σ 0 (x t) z w
  | succ n => exact barycentric_comp S G₀ G σ n x z w


/-- The full native row, not just its vertices, has its original independent source parameter. -/
theorem prespectrum_row (n : ℕ) (i : Fin (p + 1))
    (w : StdSimplex ℝ (Fin (q + 1))) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (simplex S G₀ G σ) n
      (StdSimplex.map (SimplexGrid.rowFace p q i).toOrderHom w, x) =
      prespectrumSimplexFamily S n
        (StdSimplex.single i, prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G σ) n
          (w, x)) := by
  rw [← SimplexGrid.parameter_row]
  exact prespectrum_comp S G₀ G σ n x (StdSimplex.single i) w

/-- The full native column, including level-zero loop input, is the original weak family. -/
theorem prespectrum_column (n : ℕ) (j : Fin (q + 1))
    (z : StdSimplex ℝ (Fin (p + 1))) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (simplex S G₀ G σ) n
      (StdSimplex.map (SimplexGrid.columnFace p q j).toOrderHom z, x) =
      prespectrumSimplexFamily S n
        (z, prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G σ) n
          (StdSimplex.single j, x)) := by
  rw [← SimplexGrid.parameter_column]
  exact prespectrum_comp S G₀ G σ n x z (StdSimplex.single j)

end Quillen.Waldhausen.IteratedS.ReverseMixedWeakProduct
