/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexFaces

/-!
# Adjoining an original weak transformation to a Model simplex

A selected objectwise weak natural transformation is prepended without replacing it by an
isomorphism. The complete old simplex is retained as the final face. This applies in particular
to the original transformation from the chosen zero functor to an acyclic composite.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Simplicial
universe u
namespace Quillen.Waldhausen.IteratedS.ModelSimplex
variable {V W : Model.{u}} {k : ℕ} (S : ModelSimplex V W k) {F : V ⟶ W}
  (η : F.functor ⟶ (S.vertex 0).functor)
  (hη : ∀ X, W.waldhausen.weq (η.app X))

/-- The literal original arrow followed by the entire old transformation chain. -/
def prependWeak : ModelSimplex V W (k + 1) where
  diagram := ComposableArrows.precomp S.diagram η
  exact i := by
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero => exact F.exact
    | succ i => exact S.exact ⟨i, Nat.lt_of_succ_lt_succ hi⟩
  zero i := by
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero => exact F.zero
    | succ i => exact S.zero ⟨i, Nat.lt_of_succ_lt_succ hi⟩
  weak i j f X := by
    have hij := leOfHom f
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    cases i with
    | zero =>
      cases j with
      | zero => exact W.waldhausen.weq.id_mem _
      | succ j =>
        cases j with
        | zero => exact hη X
        | succ j =>
          exact W.waldhausen.weq.comp_mem _ _ (hη X) (S.weak _ _ _ X)
    | succ i =>
      cases j with
      | zero => exact False.elim (by simp at hij)
      | succ j => exact S.weak _ _ _ X

/-- The inclusion of all original vertices, in their unchanged order. -/
def tailFace : ⦋k⦌ ⟶ ⦋k + 1⦌ :=
  SimplexCategory.Hom.mk ⟨Fin.succ, fun _ _ h ↦ Fin.succ_le_succ_iff.mpr h⟩

/-- The full old simplex, including every transformation, is an exact face. -/
theorem prependWeak_tail : (prependWeak S η hη).face tailFace = S := by
  apply ext_diagram
  rfl

/-- Repeating the original target isolates the selected arrow and an identity. -/
def firstEdgeTriangle : ⦋2⦌ ⟶ ⦋k + 1⦌ :=
  SimplexCategory.Hom.mk
    ⟨![0, 1, 1], by
      intro a b h
      fin_cases a <;> fin_cases b <;> simp_all⟩

/-- The directed first edge is the selected original transformation, not a new zero path. -/
theorem prependWeak_firstTriangle :
    (prependWeak S η hη).face firstEdgeTriangle =
      triangle η (𝟙 _) hη (fun _ ↦ W.waldhausen.weq.id_mem _) := by
  apply ext_diagram
  refine ComposableArrows.ext₂ rfl rfl rfl ?_ ?_
  · simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    rfl
  · simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    change S.diagram.map (𝟙 (0 : Fin (k + 1))) = 𝟙 _
    exact S.diagram.map_id _

end Quillen.Waldhausen.IteratedS.ModelSimplex
