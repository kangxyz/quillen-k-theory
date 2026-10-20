/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexMixedWeakProduct
public import Quillen.Topology.Realization.SimplexGridColumn
/-! # Source isomorphism families before weak simplex families -/
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
open MixedWeakProduct
variable {V W T : Model.{u}} {p q : ℕ}
variable (S : ModelSimplex W T p)
  (G₀ : V ⟶ W) (G : Fin (q + 1) → (V ⟶ W))
  (σ : ∀ i, G₀.functor ≅ (G i).functor)

/-- The full finite grid composite keeps every original weak transformation in its forward
orientation; the independently varying second chain is reindexed through its isomorphisms. -/
def simplex : ModelSimplex V T (SimplexGrid.dimension p q) :=
  (ModelSimplex.ofIsos G₀ (fun i ↦ G (secondProjection p q i))
      (fun i ↦ σ (secondProjection p q i))).diagonalComposition
    (S.face (firstProjection p q))

/-- Every whole monotone grid face is the literal composite of the two original subchains. -/
theorem grid_face {m : ℕ} (α : ⦋m⦌ ⟶ ⦋p⦌) (β : ⦋m⦌ ⟶ ⦋q⦌) :
    (simplex S G₀ G σ).face (CommonReferenceProduct.gridFace α β) =
      ((ModelSimplex.ofIsos G₀ G σ).face β).diagonalComposition (S.face α) := by
  unfold simplex
  rw [ModelSimplex.face_diagonalComposition, ModelSimplex.face_face,
    firstProjection_gridFace, ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  congr 1
  refine ModelSimplex.ofIsos_nodes_congr
    (fun i ↦ ⟨G (secondProjection p q
      ((CommonReferenceProduct.gridFace α β).toOrderHom i)),
      σ (secondProjection p q ((CommonReferenceProduct.gridFace α β).toOrderHom i))⟩)
    (fun i ↦ ⟨G (β.toOrderHom i), σ (β.toOrderHom i)⟩) ?_
  intro i
  change (⟨G (((SimplexGrid.indexEquiv p q).symm
      (SimplexGrid.index p q (α.toOrderHom i, β.toOrderHom i))).2),
    σ (((SimplexGrid.indexEquiv p q).symm
      (SimplexGrid.index p q (α.toOrderHom i, β.toOrderHom i))).2)⟩ :
      Σ J : V ⟶ W, G₀.functor ≅ J.functor) = _
  rw [SimplexGrid.decode_index]

/-- Every original iterated S-level evaluates two independent simplicial parameters by composition.
The grid parameter does not identify either time with an S-construction or structure coordinate. -/
theorem stage_comp (r : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj V).obj n) (τ : (Δ[p]).obj n) (θ : (Δ[q]).obj n) :
    stageSimplexFunction r (simplex S G₀ G σ) n A
      ((SimplexGrid.embedding p q).app n (τ, θ)) =
      stageSimplexFunction r S n
        (stageSimplexFunction r (ModelSimplex.ofIsos G₀ G σ) n A θ) τ := by
  let α := τ.down
  let β := θ.down
  let e : (Δ[n.unop.len]).obj n := ⟨𝟙 n.unop⟩
  have hα : (⟨e.down ≫ α⟩ : (Δ[p]).obj n) = τ := by
    apply ULift.ext
    exact Category.id_comp _
  have hβ : (⟨e.down ≫ β⟩ : (Δ[q]).obj n) = θ := by
    apply ULift.ext
    exact Category.id_comp _
  calc
    _ = stageSimplexFunction r
        ((simplex S G₀ G σ).face (CommonReferenceProduct.gridFace α β)) n A e :=
      stageSimplexFunction_face r (simplex S G₀ G σ) (CommonReferenceProduct.gridFace α β) n A e
    _ = stageSimplexFunction r (S.face α) n
        (stageSimplexFunction r ((ModelSimplex.ofIsos G₀ G σ).face β) n A e) e := by
      rw [grid_face, stageSimplexFunction_diagonalComposition]
    _ = _ := by
      rw [← stageSimplexFunction_face r (ModelSimplex.ofIsos G₀ G σ) β n A e]
      rw [hβ]
      simpa only [hα] using
        (stageSimplexFunction_face r S α n
          (stageSimplexFunction r (ModelSimplex.ofIsos G₀ G σ) n A θ) e).symm

/-- The whole simplicial family keeps the actual product of its two independent parameters. -/
def embedding (p q : ℕ) : (Δ[q] ⊗ Δ[p] : SSet.{u}) ⟶
    Δ[SimplexGrid.dimension p q] :=
  lift (snd _ _) (fst _ _) ≫ SimplexGrid.embedding p q

/-- The actual source product first runs the isomorphism family, then the weak family. -/
theorem stage_transformation_comp (r : ℕ) :
    (α_ ((stages r).obj V) Δ[q] Δ[p]).hom ≫
      ((stages r).obj V) ◁ embedding p q ≫
      stageTransformationSimplex r (simplex S G₀ G σ) =
    (stageTransformationSimplex r (ModelSimplex.ofIsos G₀ G σ)) ▷ Δ[p] ≫
      stageTransformationSimplex r S := by
  ext n z : 4
  exact stage_comp S G₀ G σ r n z.1.1 z.2 z.1.2


/-- Every whole original row retains the varying source isomorphism simplex. -/
theorem row_face (i : Fin (p + 1)) :
    (simplex S G₀ G σ).face (SimplexGrid.rowFace p q i) =
      ((ModelSimplex.ofIsos G₀ G σ).face (𝟙 ⦋q⦌)).diagonalComposition
        (S.face (SimplexGrid.constantFace i)) := by
  exact grid_face S G₀ G σ (SimplexGrid.constantFace i) (𝟙 ⦋q⦌)

/-- Every whole original column retains all the original weak transformations. -/
theorem column_face (j : Fin (q + 1)) :
    (simplex S G₀ G σ).face (SimplexGrid.columnFace p q j) =
      ((ModelSimplex.ofIsos G₀ G σ).face (SimplexGrid.constantFace j)).diagonalComposition
        (S.face (𝟙 ⦋p⦌)) := by
  exact grid_face S G₀ G σ (𝟙 ⦋p⦌) (SimplexGrid.constantFace j)

end Quillen.Waldhausen.IteratedS.ReverseMixedWeakProduct
