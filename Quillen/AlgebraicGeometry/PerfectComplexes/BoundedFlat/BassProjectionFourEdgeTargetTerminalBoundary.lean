/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetTerminalRows

/-! The entire central target overlap in the full original H0 reference. -/
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
open BassH0Merge CommonReferenceNerve

/-- The actual target face preserves the original two binary triangles. -/
def terminalFace : ⦋4⦌ ⟶ ⦋30⦌ := SimplexCategory.Hom.mk ⟨terminalRow, by decide⟩

/-- Its central path retains the reversed positive and forward inverse clocks. -/
theorem terminal_parameter (t : I) :
    StdSimplex.map terminalFace.toOrderHom (BassProjectionPath.parameter t) =
      ((ProjectionRectangleParameters.K BassH0Diagram.plusFace).symm.trans
        (ProjectionRectangleParameters.K BassH0Diagram.minusFace)) t :=
  BassSupportOrder.map_two_binary terminalFace.toOrderHom 0 1 2 3 4 t

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "U" => normalizedMap (coefficientMap P f)

/-- The full terminal reference keeps its literal final associator. -/
def terminalBoundaryAnchor : (reference P f E).functor ≅
    (WholeReference.reference P b (E ≫ U)).functor :=
  isoWhiskerLeft E.functor (terminalBaseAnchor P f) ≪≫
    (Functor.associator E.functor (U).functor (BassProjectionPath.source P b).functor).symm

/-- Only the complete reference is changed, with every target node retained. -/
def terminalBoundaryNode (N : CommonReferenceNerve.Node
    (WholeReference.reference P b (E ≫ U))) : CommonReferenceNerve.Node (reference P f E) :=
  CommonReferenceProduct.reanchor (terminalBoundaryAnchor P f E) N

/-- The entire product node agrees with the original target family before realization. -/
theorem terminal_product_nodes (N : CommonReferenceNerve.Node E) (i : Fin 5) :
    nodes P f E N (terminalFace.toOrderHom i) =
      terminalBoundaryNode P f E
        (WholeReference.nodes P b (E ≫ U) (postcompNode U N) i) := by
  have hi : terminalFace.toOrderHom i = terminalRow i := rfl
  rw [hi]
  let H := BassProjectionPath.source P b
  let K := BassH0Diagram.reference P f
  let θ := terminalBaseAnchor P f
  let M := BassProjectionPath.nodes P b i
  have h₁ := CommonReferenceProduct.node_associativity (E ≫ K) E U H
    (isoWhiskerLeft E.functor θ) N M
  have h₂ := CommonReferenceProduct.node_second_reanchor (E ≫ K) E K (U ≫ H)
    θ (Iso.refl _) N (precompNode U M)
  simp only [CommonReferenceProduct.postNode, CommonReferenceProduct.preNode,
    CommonReferenceProduct.reanchor, Iso.refl_trans] at h₁ h₂
  have h := (h₁.trans h₂.symm).symm
  have hη : terminalBoundaryAnchor P f E = isoWhiskerLeft E.functor θ := by
    change isoWhiskerLeft E.functor θ ≪≫ Iso.refl _ = _
    exact Iso.trans_refl _
  have ht := terminal_nodes P f i
  change BassH0Diagram.nodes P f (terminalRow i) = preReferenceNode K U θ M at ht
  change CommonReferenceProduct.node (E ≫ K) E K (Iso.refl _) N
    (preReferenceNode K U θ M) =
    CommonReferenceProduct.node (E ≫ K) (E ≫ U) H (isoWhiskerLeft E.functor θ)
      (postcompNode U N) M at h
  rw [← ht] at h
  simpa only [nodes, terminalBoundaryNode, WholeReference.nodes,
    CommonReferenceProduct.node, CommonReferenceProduct.reanchor, hη, Iso.refl_trans,
    K, M, terminalFace, reference] using h

/-- The central target word retains the whole coefficient nerve and all original quarter clocks. -/
theorem terminal_whole_parameter
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (t : I) :
    FiniteParameter.parameter E (reference P f E) (nodes P f E)
        (y, ((ProjectionRectangleParameters.K BassH0Diagram.plusFace).symm.trans
          (ProjectionRectangleParameters.K BassH0Diagram.minusFace)) t) =
      mapParameter (terminalBoundaryNode P f E)
        (WholeReference.family P b (E ≫ U) (mapParameter (postcompNode U) y, t)) := by
  rw [← terminal_parameter, ← FiniteParameter.parameter_restrict]
  obtain ⟨k, N, z, rfl⟩ := exists_parameter E y
  change FiniteParameter.parameter E (reference P f E)
    (fun e i ↦ nodes P f E e (terminalFace.toOrderHom i))
    (CommonReferenceNerve.parameter E N z, BassProjectionPath.parameter t) =
    mapParameter (terminalBoundaryNode P f E)
      (FiniteParameter.parameter (E ≫ U) (WholeReference.reference P b (E ≫ U))
        (WholeReference.nodes P b (E ≫ U))
        (mapParameter (postcompNode U) (CommonReferenceNerve.parameter E N z),
          BassProjectionPath.parameter t))
  rw [mapParameter_parameter, FiniteParameter.parameter_characteristic,
    FiniteParameter.parameter_characteristic, mapParameter_parameter]
  apply congrArg (fun ns ↦ CommonReferenceNerve.parameter (reference P f E) ns
    (SimplexGrid.parameter.{u + 1} k 4 (z, BassProjectionPath.parameter t)))
  funext j
  exact terminal_product_nodes P f E (N ((SimplexGrid.indexEquiv k 4).symm j).1)
    ((SimplexGrid.indexEquiv k 4).symm j).2

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
