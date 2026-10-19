/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SimplexProductDiagram

/-!
# Mixed weak and isomorphism simplex products

A weak model simplex can be postcomposed with an independently varying common-reference
isomorphism simplex. The full lexicographic grid has monotone first projection, so no inverse
of any weak transformation is needed. Only the isomorphism chain uses the second vertex
projection, which need not be monotone. Every simultaneous monotone grid face is the literal
diagonal composite of the original subchains.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial
universe u
namespace Quillen.Waldhausen.IteratedS

namespace ModelSimplex

/-- Restricting both chains commutes with their literal diagonal composition. -/
theorem face_diagonalComposition {V W T : Model.{u}} {k l : ℕ}
    (S : ModelSimplex V W k) (K : ModelSimplex W T k) (α : ⦋l⦌ ⟶ ⦋k⦌) :
    (S.diagonalComposition K).face α = (S.face α).diagonalComposition (K.face α) := by
  apply ext_diagram
  rfl

/-- Iterated restriction is restriction along the composite simplex map. -/
theorem face_face {V W : Model.{u}} {k l m : ℕ} (S : ModelSimplex V W k)
    (α : ⦋l⦌ ⟶ ⦋k⦌) (β : ⦋m⦌ ⟶ ⦋l⦌) :
    (S.face α).face β = S.face (β ≫ α) := by
  apply ext_diagram
  rfl

end ModelSimplex

namespace MixedWeakProduct
variable {V W T : Model.{u}} {p q : ℕ}

/-- The quotient coordinate of the lexicographic grid is monotone. -/
def firstProjection (p q : ℕ) : ⦋SimplexGrid.dimension p q⦌ ⟶ ⦋p⦌ :=
  SimplexCategory.Hom.mk {
    toFun i := ((SimplexGrid.indexEquiv p q).symm i).1
    monotone' i j h := by
      change i.val / (q + 1) ≤ j.val / (q + 1)
      exact Nat.div_le_div_right h }

/-- The remainder coordinate is used only as a vertex function for the isomorphism chain. -/
def secondProjection (p q : ℕ) (i : Fin (SimplexGrid.dimension p q + 1)) :
    Fin (q + 1) :=
  ((SimplexGrid.indexEquiv p q).symm i).2

/-- The weak first coordinate of any whole grid face is exactly its original simplex map. -/
theorem firstProjection_gridFace {m : ℕ} (α : ⦋m⦌ ⟶ ⦋p⦌) (β : ⦋m⦌ ⟶ ⦋q⦌) :
    CommonReferenceProduct.gridFace α β ≫ firstProjection p q = α := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  exact congrArg Prod.fst (SimplexGrid.decode_index p q (α.toOrderHom i, β.toOrderHom i))

variable (S : ModelSimplex V W p)
  (G₀ : W ⟶ T) (G : Fin (q + 1) → (W ⟶ T))
  (σ : ∀ i, G₀.functor ≅ (G i).functor)

/-- The full finite grid composite keeps every original weak transformation in its forward
orientation; the independently varying second chain is reindexed through its isomorphisms. -/
def simplex : ModelSimplex V T (SimplexGrid.dimension p q) :=
  (S.face (firstProjection p q)).diagonalComposition
    (ModelSimplex.ofIsos G₀ (fun i ↦ G (secondProjection p q i))
      (fun i ↦ σ (secondProjection p q i)))

/-- Every whole monotone grid face is the literal composite of the two original subchains. -/
theorem grid_face {m : ℕ} (α : ⦋m⦌ ⟶ ⦋p⦌) (β : ⦋m⦌ ⟶ ⦋q⦌) :
    (simplex S G₀ G σ).face (CommonReferenceProduct.gridFace α β) =
      (S.face α).diagonalComposition ((ModelSimplex.ofIsos G₀ G σ).face β) := by
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
      Σ J : W ⟶ T, G₀.functor ≅ J.functor) = _
  rw [SimplexGrid.decode_index]

/-- Every original iterated S-level evaluates two independent simplicial parameters by composition.
The grid parameter does not identify either time with an S-construction or structure coordinate. -/
theorem stage_comp (r : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj V).obj n) (τ : (Δ[p]).obj n) (θ : (Δ[q]).obj n) :
    stageSimplexFunction r (simplex S G₀ G σ) n A
      ((SimplexGrid.embedding p q).app n (τ, θ)) =
      stageSimplexFunction r (ModelSimplex.ofIsos G₀ G σ) n
        (stageSimplexFunction r S n A τ) θ := by
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
    _ = stageSimplexFunction r ((ModelSimplex.ofIsos G₀ G σ).face β) n
        (stageSimplexFunction r (S.face α) n A e) e := by
      rw [grid_face, stageSimplexFunction_diagonalComposition]
    _ = _ := by
      rw [← stageSimplexFunction_face r S α n A e]
      rw [hα]
      simpa only [hβ] using
        (stageSimplexFunction_face r (ModelSimplex.ofIsos G₀ G σ) β n
          (stageSimplexFunction r S n A τ) e).symm

/-- The whole simplicial family keeps the actual product of its two independent parameters. -/
theorem stage_transformation_comp (r : ℕ) :
    (α_ ((stages r).obj V) Δ[p] Δ[q]).hom ≫
      ((stages r).obj V) ◁ SimplexGrid.embedding p q ≫
      stageTransformationSimplex r (simplex S G₀ G σ) =
    (stageTransformationSimplex r S) ▷ Δ[q] ≫
      stageTransformationSimplex r (ModelSimplex.ofIsos G₀ G σ) := by
  ext n z : 4
  exact stage_comp S G₀ G σ r n z.1.1 z.1.2 z.2

end MixedWeakProduct

end Quillen.Waldhausen.IteratedS
