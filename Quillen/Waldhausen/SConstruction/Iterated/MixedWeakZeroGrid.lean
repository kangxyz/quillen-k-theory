/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.RealizationMixedWeakProduct
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceWeakZeroFaces
public import Quillen.Waldhausen.SConstruction.Iterated.ModelZeroNormalization
public import Quillen.Topology.Realization.SimplexWeakZeroGrid

/-!
# The exact weak-zero product grid inside its finite normalization cone

The entire Model diagram of the original weak-edge/isomorphism product is an ordered face
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
namespace Quillen.Waldhausen.IteratedS.MixedWeakZeroGrid
open SimplexGrid.WeakZeroCollapse

/-- The full initial row is collapsed to the original zero vertex. -/
theorem collapse_zero_row (q : ℕ) :
    SimplexGrid.rowFace 1 q 0 ≫ collapse q = SimplexGrid.constantFace 0 := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  exact collapse_zero q j

/-- The full nonzero row skips the retained original reference and keeps all anchors. -/
theorem collapse_one_row (q : ℕ) :
    SimplexGrid.rowFace 1 q 1 ≫ collapse q =
      ModelSimplex.tailFace ≫ ModelSimplex.tailFace := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  exact collapse_one q j

variable {V W T : Model.{u}} (F : V ⟶ W)
  (η : (zeroHom V W).functor ⟶ F.functor)
  (hη : ∀ X, W.waldhausen.weq (η.app X))

/-- The actual one-dimensional original weak transformation. -/
def weakEdge : ModelSimplex V W 1 :=
  ModelSimplex.prependWeak
    (ModelSimplex.ofIsos F (fun _ : Fin 1 ↦ F) (fun _ ↦ Iso.refl _)) η hη

/-- Every original weak-edge time is retained before introducing the independent chart factor. -/
theorem weakEdge_native :
    Quillen.SimplexParameters.PathLift (weakEdge F η hη)
      (Quillen.SimplexParameters.edge 0 1) (prespectrumTransformationHomotopy η hη) :=
  ModelSimplex.prependWeak_edge_native
    (ModelSimplex.ofIsos F (fun _ : Fin 1 ↦ F) (fun _ ↦ Iso.refl _)) η hη

variable {q : ℕ} (G₀ : W ⟶ T) (G : Fin (q + 1) → (W ⟶ T))
  (τ : ∀ j, G₀.functor ≅ (G j).functor)

/-- The terminal row retains the complete postcomposition anchors. -/
def nodes (j : Fin (q + 1)) : CommonReferenceNerve.Node (F ≫ G₀) :=
  ⟨F ≫ G j, isoWhiskerLeft F.functor (τ j)⟩

/-- The common directed simplex uses the actual postwhiskered weak zero transformation. -/
def target : ModelSimplex V T (q + 2) :=
  CommonReferenceWeakZero.simplex (F ≫ G₀) (nodes F G₀ G τ)
    (ModelZeroNormalization.postZero η G₀)
    (ModelZeroNormalization.postZero_weak η hη G₀)

private theorem grid_zero_isZero (j : Fin (q + 1)) (X : V) :
    CategoryTheory.Limits.IsZero
      (((MixedWeakProduct.simplex (weakEdge F η hη) G₀ G τ).diagram.obj
        (SimplexGrid.index 1 q (0, j))).obj X) := by
  change CategoryTheory.Limits.IsZero
    ((G (((SimplexGrid.indexEquiv 1 q).symm (SimplexGrid.index 1 q (0, j))).2)).functor.obj
      (((weakEdge F η hη).diagram.obj
        (((SimplexGrid.indexEquiv 1 q).symm (SimplexGrid.index 1 q (0, j))).1)).obj X))
  rw [SimplexGrid.decode_index]
  exact T.waldhausen.isZero.of_iso (eqToIso (G j).zero)

/-- The entire positive row is the unchanged anchored normalization diagram. -/
theorem positive_face :
    (MixedWeakProduct.simplex (weakEdge F η hη) G₀ G τ).face
      (SimplexGrid.rowFace 1 q 1) =
    (target F η hη G₀ G τ).face (SimplexGrid.rowFace 1 q 1 ≫ collapse q) := by
  rw [collapse_one_row, ← ModelSimplex.face_face]
  change _ = ((ModelSimplex.prependWeak
    (CommonReferenceWeakZero.normalizationSimplex (F ≫ G₀) (nodes F G₀ G τ))
    (ModelZeroNormalization.postZero η G₀)
    (ModelZeroNormalization.postZero_weak η hη G₀)).face ModelSimplex.tailFace).face
      ModelSimplex.tailFace
  rw [ModelSimplex.prependWeak_tail, CommonReferenceWeakZero.normalization_face]
  have hrow := MixedWeakProduct.grid_face (weakEdge F η hη) G₀ G τ
    (SimplexGrid.constantFace (1 : Fin 2)) (𝟙 ⦋q⦌)
  change (MixedWeakProduct.simplex (weakEdge F η hη) G₀ G τ).face
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
    MixedWeakProduct.simplex (weakEdge F η hη) G₀ G τ =
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
    · change (MixedWeakProduct.simplex (weakEdge F η hη) G₀ G τ).diagram.obj
        (SimplexGrid.index 1 q (0, b)) = (target F η hη G₀ G τ).diagram.obj
          ((collapse q).toOrderHom (SimplexGrid.index 1 q (0, b)))
      rw [collapse_zero q b]
      change ((weakEdge F η hη).diagram.obj
        ((SimplexGrid.indexEquiv 1 q).symm (SimplexGrid.index 1 q (0, b))).1 ⋙
        (G (((SimplexGrid.indexEquiv 1 q).symm
          (SimplexGrid.index 1 q (0, b))).2)).functor) = _
      rw [SimplexGrid.decode_index]
      exact congrArg Model.Hom.functor (ModelZeroNormalization.zero_postcomp (G b)).symm
    · change (MixedWeakProduct.simplex (weakEdge F η hη) G₀ G τ).diagram.obj
        (SimplexGrid.index 1 q (1, b)) = (target F η hη G₀ G τ).diagram.obj
          ((collapse q).toOrderHom (SimplexGrid.index 1 q (1, b)))
      rw [collapse_one q b]
      change ((weakEdge F η hη).diagram.obj
        ((SimplexGrid.indexEquiv 1 q).symm (SimplexGrid.index 1 q (1, b))).1 ⋙
        (G (((SimplexGrid.indexEquiv 1 q).symm
          (SimplexGrid.index 1 q (1, b))).2)).functor) = _
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

/-- The actual two-parameter product realizes in the collapsed cone, without affine replacement. -/
theorem native (n : ℕ) (x : (prespectrum V).space n)
    (z : StdSimplex ℝ (Fin 2)) (w : StdSimplex ℝ (Fin (q + 1))) :
    prespectrumSimplexFamily (target F η hη G₀ G τ) n
      (parameter.{u} (z, w), x) =
      prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G τ) n
        (w, prespectrumSimplexFamily (weakEdge F η hη) n (z, x)) := by
  change prespectrumSimplexFamily (target F η hη G₀ G τ) n
    (StdSimplex.map (collapse q).toOrderHom (SimplexGrid.parameter 1 q (z, w)), x) = _
  rw [prespectrumSimplexFamily_face, ← simplex_eq]
  exact MixedWeakProduct.prespectrum_comp (weakEdge F η hη) G₀ G τ n x z w

/-- The independent normalization family follows the unchanged original reversed weak edge. -/
theorem native_null (n : ℕ) (r : unitInterval)
    (w : StdSimplex ℝ (Fin (q + 1))) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (target F η hη G₀ G τ) n
      (parameter.{u} ((Quillen.SimplexParameters.edge (k := 1) 0 1).symm r, w), x) =
      prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G τ) n
        (w, (prespectrumTransformationHomotopy η hη).level n (unitInterval.symm r, x)) := by
  rw [native]
  exact congrArg (fun y ↦ prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G τ) n (w, y))
    (weakEdge_native F η hη n (unitInterval.symm r) x)

end Quillen.Waldhausen.IteratedS.MixedWeakZeroGrid
