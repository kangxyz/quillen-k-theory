/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceWhiskering

/-! Composition of two chains at the same simplicial parameter. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
open scoped Simplicial
universe u
namespace Quillen.Waldhausen.IteratedS.ModelSimplex
variable {V W T : Model.{u}} {k : ℕ}

/-- The literal diagonal composite of two model diagrams, with horizontal composition maps. -/
def diagonalComposition (S : ModelSimplex V W k) (K : ModelSimplex W T k) :
    ModelSimplex V T k where
  diagram := S.diagram.prod' K.diagram ⋙ Functor.uncurry.obj (whiskeringLeft V W T)
  exact i := (S.exact i).comp (K.exact i)
  zero i := (congrArg (K.diagram.obj i).obj (S.zero i)).trans (K.zero i)
  weak i j f X := by
    change T.waldhausen.weq
      (((K.diagram.obj i).map ((S.diagram.map f).app X)) ≫
        (K.diagram.map f).app ((S.diagram.obj j).obj X))
    exact T.waldhausen.weq.comp_mem _ _
      ((K.exact i).weak _ (S.weak i j f X)) (K.weak i j f _)

/-- Composition is preserved on the actual quotient-row model diagrams. -/
theorem rows_diagonalComposition (S : ModelSimplex V W k) (K : ModelSimplex W T k)
    (n : SimplexCategory) :
    (S.diagonalComposition K).rows n = (S.rows n).diagonalComposition (K.rows n) := by
  apply ext_diagram
  refine CategoryTheory.Functor.hext (fun i ↦ ?_) ?_
  · exact congrArg Model.Hom.functor ((IteratedS.rows n).map_comp (S.vertex i) (K.vertex i))
  · intro i j f
    apply heq_of_eq
    apply NatTrans.ext
    funext A
    apply ObjectProperty.hom_ext
    ext p
    rfl

/-- Common-reference construction commutes with actual diagonal composition. -/
theorem diagonalComposition_ofIsos (F₀ : V ⟶ W) (F : Fin (k + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.functor ≅ (F i).functor)
    (G₀ : W ⟶ T) (G : Fin (k + 1) → (W ⟶ T))
    (σ : ∀ i, G₀.functor ≅ (G i).functor) :
    (ofIsos F₀ F ρ).diagonalComposition (ofIsos G₀ G σ) =
      ofIsos (F₀ ≫ G₀) (fun i ↦ F i ≫ G i)
        (fun i ↦ (Functor.uncurry.obj (whiskeringLeft V W T)).mapIso ((ρ i).prod (σ i))) := by
  apply ext_diagram
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro i j f
  apply heq_of_eq
  change (Functor.uncurry.obj (whiskeringLeft V W T)).map
    (CategoryTheory.Prod.mkHom ((ρ i).inv ≫ (ρ j).hom) ((σ i).inv ≫ (σ j).hom)) =
    (Functor.uncurry.obj (whiskeringLeft V W T)).map ((ρ i).prod (σ i)).inv ≫
      (Functor.uncurry.obj (whiskeringLeft V W T)).map ((ρ j).prod (σ j)).hom
  rw [← Functor.map_comp]
  rfl

end Quillen.Waldhausen.IteratedS.ModelSimplex

namespace Quillen.Waldhausen.IteratedS
open Opposite

/-- Evaluation of a diagonal composite is literal composition at the same simplicial parameter,
at every iterated S-level. -/
theorem stageSimplexFunction_diagonalComposition (r : ℕ)
    {V W T : Model.{u}} {k : ℕ} (S : ModelSimplex V W k) (K : ModelSimplex W T k)
    (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj V).obj n) (τ : (Δ[k]).obj n) :
    stageSimplexFunction r (S.diagonalComposition K) n A τ =
      stageSimplexFunction r K n (stageSimplexFunction r S n A τ) τ := by
  induction r generalizing V W T with
  | zero =>
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro X Y f
    simp [stageSimplexFunction, weakNaturalTransformationSimplex, nerveSimplexDiagram,
      ModelSimplex.diagonalComposition, Functor.uncurry, Functor.map_comp, Category.assoc]
  | succ r ih =>
    change stageSimplexFunction r ((S.diagonalComposition K).rows n.unop) n A τ = _
    rw [ModelSimplex.rows_diagonalComposition]
    exact ih (S.rows n.unop) (K.rows n.unop) A

end Quillen.Waldhausen.IteratedS
