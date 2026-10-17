/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetSourceRows

/-!
# The complete source boundary of the original target comparison

The ordered source face contains the original two-chart Bass projection path at its unchanged
four-quarter clock. Its whole coefficient-nerve product is the original source family followed
by the Laurent coefficient map. The full H0 normalization, projection equality, left whiskering,
and literal associator are retained in the target anchor before passage to realization.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u

namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
open BassH0Merge BassH1Join CommonReferenceNerve CoefficientBassSeedTargetH0Reference

private theorem product_post_reference {V W W' T : Model.{u}}
    (E : V ⟶ W) (H : W ⟶ W') (K : W ⟶ T) (J : W' ⟶ T)
    (θ : K.functor ≅ (H ≫ J).functor)
    (N : CommonReferenceNerve.Node E) (M : CommonReferenceNerve.Node H) :
    CommonReferenceProduct.node (E ≫ K) E K (Iso.refl _) N (postReferenceNode K J θ M) =
      postReferenceNode (E ≫ K) J (isoWhiskerLeft E.functor θ)
        (CommonReferenceProduct.node (E ≫ H) E H (Iso.refl _) N M) := by
  have h₁ := CommonReferenceProduct.node_second_reanchor (E ≫ K) E K (H ≫ J)
    θ (Iso.refl _) N (postcompNode J M)
  have h₂ := CommonReferenceProduct.node_postcomp (E ≫ K) E H J
    (isoWhiskerLeft E.functor θ) N M
  simp only [CommonReferenceProduct.postNode, CommonReferenceProduct.reanchor,
    Iso.refl_trans] at h₁ h₂
  exact h₁.trans h₂

private theorem parameter_target_map {V W V' W' V'' W'' : Model.{u}}
    (E : V ⟶ W) (D : V' ⟶ W') (F : V'' ⟶ W'') {q : ℕ}
    (g : CommonReferenceNerve.Node E → Fin (q + 1) → CommonReferenceNerve.Node D)
    (h : CommonReferenceNerve.Node D → CommonReferenceNerve.Node F)
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|)
    (z : StdSimplex ℝ (Fin (q + 1))) :
    mapParameter h (FiniteParameter.parameter E D g (y, z)) =
      FiniteParameter.parameter E F (fun e i ↦ h (g e i)) (y, z) := by
  obtain ⟨k, N, w, rfl⟩ := exists_parameter E y
  rw [FiniteParameter.parameter_characteristic, mapParameter_parameter,
    FiniteParameter.parameter_characteristic]
  rfl

/-- The ordered source face retains both distinct raw normalization intermediates. -/
def sourceFace : ⦋4⦌ ⟶ ⦋30⦌ := SimplexCategory.Hom.mk ⟨sourceRow, by decide⟩

/-- The original Bass clock maps exactly to the reversed positive and forward inverse columns. -/
theorem source_parameter (t : I) :
    StdSimplex.map sourceFace.toOrderHom (BassProjectionPath.parameter t) =
      ((ProjectionRectangleParameters.D BassH0Diagram.plusFace).symm.trans
        (ProjectionRectangleParameters.D BassH0Diagram.minusFace)) t :=
  BassSupportOrder.map_two_binary sourceFace.toOrderHom 0 1 2 3 4 t

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)

/-- The complete source face has the original five dependent nodes with its exact H0 anchor. -/
theorem source_row_parameter (z : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter (BassH0Diagram.reference P f) (BassH0Diagram.nodes P f)
      (StdSimplex.map sourceFace.toOrderHom z) =
    CommonReferenceNerve.parameter (BassH0Diagram.reference P f) (fun i ↦
      postReferenceNode (BassH0Diagram.reference P f) (sourcePost P f) (h0ProjectionIso P f)
        (BassProjectionPath.nodes P a i)) z := by
  rw [CommonReferenceNerve.parameter_face]
  exact congrArg (fun N ↦ CommonReferenceNerve.parameter (BassH0Diagram.reference P f) N z)
    (funext (source_nodes P f))

variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))

/-- The entire source boundary anchor retains the H0 reference and literal associator. -/
def sourceBoundaryAnchor : (reference P f E).functor ≅
    (WholeReference.reference P a E ≫ sourcePost P f).functor :=
  isoWhiskerLeft E.functor (h0ProjectionIso P f) ≪≫
    (Functor.associator E.functor (BassProjectionPath.source P a).functor
      (sourcePost P f).functor).symm

/-- The original Laurent coefficient map acts on complete nodes in the source reference. -/
def sourceBoundaryNode (N : CommonReferenceNerve.Node (WholeReference.reference P a E)) :
    CommonReferenceNerve.Node (reference P f E) :=
  postReferenceNode (reference P f E) (sourcePost P f) (sourceBoundaryAnchor P f E) N

/-- The complete product source row agrees before realization or native evaluation. -/
theorem source_product_nodes (N : CommonReferenceNerve.Node E) (i : Fin 5) :
    nodes P f E N (sourceFace.toOrderHom i) =
      sourceBoundaryNode P f E (WholeReference.nodes P a E N i) := by
  have h := product_post_reference E (BassProjectionPath.source P a)
    (BassH0Diagram.reference P f) (sourcePost P f) (h0ProjectionIso P f) N
    (BassProjectionPath.nodes P a i)
  rw [← source_nodes P f i] at h
  have hη : sourceBoundaryAnchor P f E = isoWhiskerLeft E.functor (h0ProjectionIso P f) := by
    change isoWhiskerLeft E.functor (h0ProjectionIso P f) ≪≫ Iso.refl _ = _
    exact Iso.trans_refl _
  change (⟨N.1 ≫ (BassH0Diagram.nodes P f (sourceRow i)).1,
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      (N.2.prod (BassH0Diagram.nodes P f (sourceRow i)).2)⟩ :
      CommonReferenceNerve.Node (E ≫ BassH0Diagram.reference P f)) =
    postReferenceNode (E ≫ BassH0Diagram.reference P f) (sourcePost P f)
      (sourceBoundaryAnchor P f E) (WholeReference.nodes P a E N i)
  simpa only [WholeReference.nodes, CommonReferenceProduct.node, hη, Iso.refl_trans] using h

/-- The whole initial overlap is the original source family under its full postcomposition map. -/
theorem overlap_source (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (t : I) :
    overlap P f E (y, (0, t)) =
      mapParameter (sourceBoundaryNode P f E) (WholeReference.family P a E (y, t)) := by
  calc
    _ = FiniteParameter.parameter E (reference P f E) (nodes P f E)
        (y, ((ProjectionRectangleParameters.D BassH0Diagram.plusFace).symm.trans
          (ProjectionRectangleParameters.D BassH0Diagram.minusFace)) t) :=
      overlap_zero P f E y t
    _ = FiniteParameter.parameter E (reference P f E)
        (fun N i ↦ nodes P f E N (sourceFace.toOrderHom i))
        (y, BassProjectionPath.parameter t) := by
      rw [FiniteParameter.parameter_restrict, source_parameter]
    _ = FiniteParameter.parameter E (reference P f E)
        (fun N i ↦ sourceBoundaryNode P f E (WholeReference.nodes P a E N i))
        (y, BassProjectionPath.parameter t) :=
      congrArg (fun g ↦ FiniteParameter.parameter E (reference P f E) g
        (y, BassProjectionPath.parameter t))
        (funext (fun N ↦ funext (source_product_nodes P f E N)))
    _ = _ := (parameter_target_map E (WholeReference.reference P a E) (reference P f E)
      (WholeReference.nodes P a E) (sourceBoundaryNode P f E) y
        (BassProjectionPath.parameter t)).symm

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
