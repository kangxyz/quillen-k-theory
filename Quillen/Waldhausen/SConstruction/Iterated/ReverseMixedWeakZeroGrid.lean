/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.RealizationReverseMixedWeakProduct
public import Quillen.Waldhausen.SConstruction.Iterated.MixedWeakZeroGrid
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceWeakZeroFaces
public import Quillen.Waldhausen.SConstruction.Iterated.ModelZeroNormalization
public import Quillen.Topology.Realization.SimplexWeakZeroGrid

/-!
# The exact source-isomorphism and weak-zero product grid

The entire Model diagram of the original source-isomorphism/weak-edge product is an ordered face
of the common weak-zero simplex. The positive row preserves complete whiskered anchors;
chosen-zero transport and source uniqueness identify the initial row and every outgoing arrow.
The full native product and reversed-null time are recovered at the original product parameter.
No equality with an independently chosen affine-cone interior is asserted.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Convexity
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.ReverseMixedWeakZeroGrid
open SimplexGrid.WeakZeroCollapse

open MixedWeakZeroGrid (collapse_zero_row collapse_one_row weakEdge weakEdge_native)

variable {V W T : Model.{u}} (F : W ⟶ T)
  (η : (zeroHom W T).functor ⟶ F.functor)
  (hη : ∀ X, T.waldhausen.weq (η.app X))

variable {q : ℕ} (G₀ : V ⟶ W) (G : Fin (q + 1) → (V ⟶ W))
  (τ : ∀ j, G₀.functor ≅ (G j).functor)

/-- The terminal row retains the complete precomposition anchors. -/
def nodes (j : Fin (q + 1)) : CommonReferenceNerve.Node (G₀ ≫ F) :=
  ⟨G j ≫ F, isoWhiskerRight (τ j) F.functor⟩

/-- The common directed simplex uses the actual prewhiskered weak zero transformation. -/
def target : ModelSimplex V T (q + 2) :=
  CommonReferenceWeakZero.simplex (G₀ ≫ F) (nodes F G₀ G τ)
    (ModelZeroNormalization.preZero η G₀)
    (ModelZeroNormalization.preZero_weak η hη G₀)

private theorem grid_zero_isZero (j : Fin (q + 1)) (X : V) :
    CategoryTheory.Limits.IsZero
      (((ReverseMixedWeakProduct.simplex (weakEdge F η hη) G₀ G τ).diagram.obj
        (SimplexGrid.index 1 q (0, j))).obj X) := by
  change CategoryTheory.Limits.IsZero
    (((weakEdge F η hη).diagram.obj
      (((SimplexGrid.indexEquiv 1 q).symm (SimplexGrid.index 1 q (0, j))).1)).obj
        ((G (((SimplexGrid.indexEquiv 1 q).symm
          (SimplexGrid.index 1 q (0, j))).2)).functor.obj X))
  rw [SimplexGrid.decode_index]
  exact T.waldhausen.isZero

/-- The entire positive row is the unchanged anchored normalization diagram. -/
theorem positive_face :
    (ReverseMixedWeakProduct.simplex (weakEdge F η hη) G₀ G τ).face
      (SimplexGrid.rowFace 1 q 1) =
    (target F η hη G₀ G τ).face (SimplexGrid.rowFace 1 q 1 ≫ collapse q) := by
  rw [collapse_one_row, ← ModelSimplex.face_face]
  change _ = ((ModelSimplex.prependWeak
    (CommonReferenceWeakZero.normalizationSimplex (G₀ ≫ F) (nodes F G₀ G τ))
    (ModelZeroNormalization.preZero η G₀)
    (ModelZeroNormalization.preZero_weak η hη G₀)).face ModelSimplex.tailFace).face
      ModelSimplex.tailFace
  rw [ModelSimplex.prependWeak_tail, CommonReferenceWeakZero.normalization_face]
  have hrow := ReverseMixedWeakProduct.grid_face (weakEdge F η hη) G₀ G τ
    (SimplexGrid.constantFace (1 : Fin 2)) (𝟙 ⦋q⦌)
  change (ReverseMixedWeakProduct.simplex (weakEdge F η hη) G₀ G τ).face
    (SimplexGrid.rowFace 1 q 1) = _ at hrow
  rw [hrow]
  apply ModelSimplex.ext_diagram
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j f
  ext X
  simp [ModelSimplex.diagonalComposition, ModelSimplex.face, SimplexGrid.constantFace,
    weakEdge, ModelSimplex.prependWeak, ModelSimplex.ofIsos, nodes, Functor.uncurry]

/-- The full grid diagram is the face collapsing its original zero row. -/
theorem simplex_eq :
    ReverseMixedWeakProduct.simplex (weakEdge F η hη) G₀ G τ =
      (target F η hη G₀ G τ).face (collapse q) := by
  have surj : Function.Surjective (SimplexGrid.index 1 q) := by
    intro i
    obtain ⟨z, hz⟩ := (SimplexGrid.indexEquiv 1 q).surjective i
    exact ⟨z, (SimplexGrid.index_eq_equiv 1 q z).trans hz⟩
  apply ModelSimplex.ext_diagram
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · obtain ⟨⟨a, b⟩, rfl⟩ := surj i
    change _ = (target F η hη G₀ G τ).diagram.obj
      ((collapse q).toOrderHom (SimplexGrid.index 1 q (a, b)))
    fin_cases a <;> dsimp only
    · change (ReverseMixedWeakProduct.simplex (weakEdge F η hη) G₀ G τ).diagram.obj
        (SimplexGrid.index 1 q (0, b)) = (target F η hη G₀ G τ).diagram.obj
          ((collapse q).toOrderHom (SimplexGrid.index 1 q (0, b)))
      rw [collapse_zero q b]
      change ((G (((SimplexGrid.indexEquiv 1 q).symm
          (SimplexGrid.index 1 q (0, b))).2)).functor ⋙
        (weakEdge F η hη).diagram.obj
          ((SimplexGrid.indexEquiv 1 q).symm (SimplexGrid.index 1 q (0, b))).1) = _
      rw [SimplexGrid.decode_index]
      exact congrArg Model.Hom.functor (ModelZeroNormalization.zero_precomp (G b)).symm
    · change (ReverseMixedWeakProduct.simplex (weakEdge F η hη) G₀ G τ).diagram.obj
        (SimplexGrid.index 1 q (1, b)) = (target F η hη G₀ G τ).diagram.obj
          ((collapse q).toOrderHom (SimplexGrid.index 1 q (1, b)))
      rw [collapse_one q b]
      change ((G (((SimplexGrid.indexEquiv 1 q).symm
          (SimplexGrid.index 1 q (1, b))).2)).functor ⋙
        (weakEdge F η hη).diagram.obj
          ((SimplexGrid.indexEquiv 1 q).symm (SimplexGrid.index 1 q (1, b))).1) = _
      rw [SimplexGrid.decode_index]
      rfl
  · intro i j f
    have hij := leOfHom f
    obtain ⟨⟨a, b⟩, rfl⟩ := surj i
    obtain ⟨⟨c, d⟩, rfl⟩ := surj j
    fin_cases a <;> fin_cases c
    · ext X
      exact (grid_zero_isZero F η hη G₀ G τ b X).eq_of_src _ _
    · ext X
      exact (grid_zero_isZero F η hη G₀ G τ b X).eq_of_src _ _
    · have hb := b.isLt
      change (1 : ℕ) * (q + 1) + b.val ≤ 0 * (q + 1) + d.val at hij
      have hd := d.isLt
      omega
    · have hbd : b ≤ d := by
        change 1 * (q + 1) + b.val ≤ 1 * (q + 1) + d.val at hij
        change b.val ≤ d.val
        omega
      exact CategoryTheory.Functor.congr_hom
        (congrArg ModelSimplex.diagram (positive_face F η hη G₀ G τ)) (homOfLE hbd)

/-- The original product, not an affine replacement, realizes in the collapsed cone. -/
theorem native (n : ℕ) (x : (prespectrum V).space n)
    (z : StdSimplex ℝ (Fin 2)) (w : StdSimplex ℝ (Fin (q + 1))) :
    prespectrumSimplexFamily (target F η hη G₀ G τ) n (parameter.{u} (z, w), x) =
      prespectrumSimplexFamily (weakEdge F η hη) n
        (z, prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G τ) n (w, x)) := by
  change prespectrumSimplexFamily (target F η hη G₀ G τ) n
    (StdSimplex.map (collapse q).toOrderHom (SimplexGrid.parameter 1 q (z, w)), x) = _
  rw [prespectrumSimplexFamily_face, ← simplex_eq]
  exact ReverseMixedWeakProduct.prespectrum_comp (weakEdge F η hη) G₀ G τ n x z w

/-- The unchanged reversed weak edge follows the whole independent source normalization family. -/
theorem native_null (n : ℕ) (r : unitInterval)
    (w : StdSimplex ℝ (Fin (q + 1))) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (target F η hη G₀ G τ) n
      (parameter.{u} ((Quillen.SimplexParameters.edge (k := 1) 0 1).symm r, w), x) =
      (prespectrumTransformationHomotopy η hη).level n
        (unitInterval.symm r,
          prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G τ) n (w, x)) := by
  rw [native]
  exact weakEdge_native F η hη n (unitInterval.symm r)
    (prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G τ) n (w, x))

end Quillen.Waldhausen.IteratedS.ReverseMixedWeakZeroGrid
