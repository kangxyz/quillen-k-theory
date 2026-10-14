/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SimplexFamily
public import Quillen.Waldhausen.SConstruction.Iterated.TriangleComposition

/-!
# Original iterated triangle faces of the higher simplex family

Exact correspondence of the higher family with the maintained original iterated triangles. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS
namespace ModelSimplex

/-- The original two-arrow chain as a higher-family input. -/
def triangle {V W : Model.{u}} {F G H : V ⟶ W}
    (η : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
    (hη : ∀ A, W.waldhausen.weq (η.app A)) (hθ : ∀ A, W.waldhausen.weq (θ.app A)) :
    ModelSimplex V W 2 where
  diagram := ComposableArrows.mk₂ η θ
  exact i := by
    fin_cases i
    · exact F.exact
    · exact G.exact
    · exact H.exact
  zero i := by
    fin_cases i
    · exact F.zero
    · exact G.zero
    · exact H.zero
  weak i j f A := by
    have hf := leOfHom f
    fin_cases i <;> fin_cases j
    · change W.waldhausen.weq (𝟙 (F.functor.obj A))
      exact W.waldhausen.weq.id_mem _
    · exact hη A
    · exact W.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)
    · exact False.elim ((by decide : ¬ (1 : Fin 3) ≤ 0) hf)
    · change W.waldhausen.weq (𝟙 (G.functor.obj A))
      exact W.waldhausen.weq.id_mem _
    · exact hθ A
    · exact False.elim ((by decide : ¬ (2 : Fin 3) ≤ 0) hf)
    · exact False.elim ((by decide : ¬ (2 : Fin 3) ≤ 1) hf)
    · change W.waldhausen.weq (𝟙 (H.functor.obj A))
      exact W.waldhausen.weq.id_mem _

/-- Passing to actual quotient rows retains the entire original two-arrow chain. -/
theorem rows_triangle {V W : Model.{u}} {F G H : V ⟶ W}
    (η : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
    (hη : ∀ A, W.waldhausen.weq (η.app A)) (hθ : ∀ A, W.waldhausen.weq (θ.app A))
    (n : SimplexCategory) :
    (triangle η θ hη hθ).rows n =
      triangle (rowsTransformation η n) (rowsTransformation θ n)
        (rowsTransformation_weak η hη n) (rowsTransformation_weak θ hθ n) := by
  apply ext_diagram
  refine ComposableArrows.ext₂
    (f := ((triangle η θ hη hθ).rows n).diagram)
    (g := (triangle (rowsTransformation η n) (rowsTransformation θ n)
      (rowsTransformation_weak η hη n) (rowsTransformation_weak θ hθ n)).diagram)
    rfl rfl rfl ?_ ?_ <;> simp <;> rfl

/-- Every two-dimensional face is exactly its original chain of adjacent transformations. -/
theorem triangle_reconstruct {V W : Model.{u}} (S : ModelSimplex V W 2) :
    S = triangle (F := S.vertex 0) (G := S.vertex 1) (H := S.vertex 2)
      (S.diagram.map (homOfLE (by decide : (0 : Fin 3) ≤ 1)))
      (S.diagram.map (homOfLE (by decide : (1 : Fin 3) ≤ 2)))
      (S.weak _ _ _) (S.weak _ _ _) := by
  apply ext_diagram
  refine ComposableArrows.ext₂ (f := S.diagram)
    (g := ComposableArrows.mk₂
      (S.diagram.map (homOfLE (by decide : (0 : Fin 3) ≤ 1)))
      (S.diagram.map (homOfLE (by decide : (1 : Fin 3) ≤ 2))))
    rfl rfl rfl ?_ ?_ <;> simp

end ModelSimplex

private theorem mk₂_whiskerLeft_simplex {K C D : Type*} [Category* K] [Category* C] [Category* D]
    (J : K ⥤ C) {F G H : C ⥤ D} (η : F ⟶ G) (θ : G ⟶ H) :
    ComposableArrows.mk₂ (whiskerLeft J η) (whiskerLeft J θ) =
      ComposableArrows.mk₂ η θ ⋙ (whiskeringLeft K C D).obj J := by
  apply ComposableArrows.ext₂
    (f := ComposableArrows.mk₂ (whiskerLeft J η) (whiskerLeft J θ))
    (g := ComposableArrows.mk₂ η θ ⋙ (whiskeringLeft K C D).obj J) rfl rfl rfl <;> simp

/-- The higher family contains every point of the original iterated triangle. -/
theorem stageSimplexFunction_triangle (r : ℕ) {V W : Model.{u}} {F G H : V ⟶ W}
    (η : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
    (hη : ∀ A, W.waldhausen.weq (η.app A)) (hθ : ∀ A, W.waldhausen.weq (θ.app A))
    (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj V).obj n) (τ : (Δ[2]).obj n) :
    stageSimplexFunction r (ModelSimplex.triangle η θ hη hθ) n A τ =
      stageTriangleFunction r η θ hη hθ n A τ := by
  induction r generalizing V W with
  | zero =>
    apply Subtype.ext
    change nerveSimplexDiagram
      (ComposableArrows.mk₂ η θ ⋙ (whiskeringLeft _ V W).obj A.val) τ.down = _
    rw [← mk₂_whiskerLeft_simplex]
    rfl
  | succ r ih =>
    change stageSimplexFunction r ((ModelSimplex.triangle η θ hη hθ).rows n.unop)
      n A τ = _
    rw [ModelSimplex.rows_triangle]
    exact ih (rowsTransformation η n.unop) (rowsTransformation θ n.unop)
      (rowsTransformation_weak η hη n.unop) (rowsTransformation_weak θ hθ n.unop) A

/-- The old simplex is retained as an equality of entire simplicial transformation families. -/
theorem stageTransformationSimplex_triangle (r : ℕ) {V W : Model.{u}} {F G H : V ⟶ W}
    (η : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
    (hη : ∀ A, W.waldhausen.weq (η.app A)) (hθ : ∀ A, W.waldhausen.weq (θ.app A)) :
    stageTransformationSimplex r (ModelSimplex.triangle η θ hη hθ) =
      stageTransformationTriangle r η θ hη hθ := by
  ext n z : 4
  exact stageSimplexFunction_triangle r η θ hη hθ n z.1 z.2

/-- All continuous values of the original triangle are retained by the higher family. -/
theorem stageSimplexRealization_triangle (r : ℕ) {V W : Model.{u}} {F G H : V ⟶ W}
    (η : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
    (hη : ∀ A, W.waldhausen.weq (η.app A)) (hθ : ∀ A, W.waldhausen.weq (θ.app A)) :
    stageSimplexRealization r (ModelSimplex.triangle η θ hη hθ) =
      stageTriangleRealization η θ hη hθ r := by
  unfold stageSimplexRealization stageTriangleRealization
  rw [stageTransformationSimplex_triangle]

/-- Every geometric simplex face realizes the exact original subchain family. -/
theorem stageSimplexRealization_face (r : ℕ) {V W : Model.{u}} {k l : ℕ}
    (S : ModelSimplex V W k) (α : ⦋l⦌ ⟶ ⦋k⦌)
    (x : stageSpace r V) (z : |(Δ[l] : SSet.{u})|) :
    stageSimplexRealization r S (x, SSet.toTop.map (SSet.stdSimplex.map α) z) =
      stageSimplexRealization r (S.face α) (x, z) := by
  have hp := ConcreteCategory.congr_hom
    (TheoremB.realizationProductSimplexIso_inv_naturality (𝟙 ((stages r).obj V)) α) (x, z)
  have hv : (SSet.toTop.map (𝟙 ((stages r).obj V)) ⊗ₘ
      SSet.toTop.map (SSet.stdSimplex.map α)) (x, z) =
      (x, SSet.toTop.map (SSet.stdSimplex.map α) z) := by simp
  rw [TopCat.comp_app, TopCat.comp_app, hv] at hp
  change SSet.toTop.map (stageTransformationSimplex r S)
    ((realizationProductSimplexIso ((stages r).obj V) k).inv
      (x, SSet.toTop.map (SSet.stdSimplex.map α) z)) = _
  rw [← hp]
  change (SSet.toTop.map ((𝟙 ((stages r).obj V)) ⊗ₘ SSet.stdSimplex.map α) ≫
    SSet.toTop.map (stageTransformationSimplex r S))
      ((realizationProductSimplexIso ((stages r).obj V) l).inv (x, z)) = _
  rw [← Functor.map_comp, stageTransformationSimplex_face]
  rfl

end Quillen.Waldhausen.IteratedS
