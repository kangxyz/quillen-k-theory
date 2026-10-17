/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeReanchorCone
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeExt
public import Quillen.Aglib.Topology.Path.EvaluationOperations

/-! Every original tree edge and cone coordinate survives full input reanchoring. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open MonoidalCategory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Reanchor
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier FourEdgeTree

private theorem edge_precomp {X Y Z : SSet.{u}} (f : X ⟶ Y) (H : Y ⊗ Δ[1] ⟶ Z)
    (y : |X|) (t : I) : realizedEdge (f ▷ Δ[1] ≫ H) (y, t) =
      realizedEdge H (SSet.toTop.map f y, t) := by
  have h := ConcreteCategory.congr_hom (realizationCylinderIso_inv_naturality f)
    (y, ULift.up t)
  change SSet.toTop.map (f ▷ Δ[1]) ((realizationCylinderIso X).inv (y, ULift.up t)) =
    (realizationCylinderIso Y).inv (SSet.toTop.map f y, ULift.up t) at h
  exact (realized_comp (f ▷ Δ[1]) H _).trans (congrArg (SSet.toTop.map H) h)

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {V : Model.{u + 1}}
  (E E' : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
  (δ : E'.functor ≅ E.functor)
local notation "J" => normalizedMap (polynomialProjection P a)
local notation "F" => reference P a E
local notation "F'" => reference P a E'
local notation "β" => beta P a E
local notation "β'" => beta P a E'

/-- The continuous four-edge tree map obtained by reanchoring from `E` to `E'` along `δ`. -/
def tree : C(FourEdgeTree.space E J, FourEdgeTree.space E' J) :=
  (SSet.toTop.map (map P a E E' δ)).hom

theorem tree_plus (y : |parameterSSet (E ≫ J)|) :
    tree P a E E' δ (SSet.toTop.map (plusVertex E J) y) =
      SSet.toTop.map (plusVertex E' J) (mapParameter (CommonReferenceProduct.reanchor
        (isoWhiskerRight δ (J).functor)) y) := by
  change SSet.toTop.map (map P a E E' δ) _ = _
  rw [← realized_comp, map_plus, realized_comp]; rfl

theorem tree_minus (y : |parameterSSet (E ≫ J)|) :
    tree P a E E' δ (SSet.toTop.map (minusVertex E J) y) =
      SSet.toTop.map (minusVertex E' J) (mapParameter (CommonReferenceProduct.reanchor
        (isoWhiskerRight δ (J).functor)) y) := by
  change SSet.toTop.map (map P a E E' δ) _ = _
  rw [← realized_comp, map_minus, realized_comp]; rfl

theorem tree_edge12 (y : |parameterSSet E|) (t : I) :
    tree P a E E' δ (realizedEdge (edge12 E J) (y, t)) =
      realizedEdge (edge12 E' J) (mapParameter (CommonReferenceProduct.reanchor δ) y, t) := by
  change SSet.toTop.map (map P a E E' δ) _ = _
  rw [← realizedEdge_comp, map_edge12, edge_precomp]; rfl

theorem tree_edge01 (y : |parameterSSet E|) (t : I) :
    tree P a E E' δ (realizedEdge (edge01 E J) (y, t)) =
      realizedEdge (edge01 E' J) (mapParameter (CommonReferenceProduct.reanchor δ) y, t) := by
  change SSet.toTop.map (map P a E E' δ) _ = _
  rw [← realizedEdge_comp, map_edge01, edge_precomp]; rfl

theorem tree_edge03 (y : |parameterSSet E|) (t : I) :
    tree P a E E' δ (realizedEdge (edge03 E J) (y, t)) =
      realizedEdge (edge03 E' J) (mapParameter (CommonReferenceProduct.reanchor δ) y, t) := by
  change SSet.toTop.map (map P a E E' δ) _ = _
  rw [← realizedEdge_comp, map_edge03, edge_precomp]; rfl

theorem tree_edge34 (y : |parameterSSet E|) (t : I) :
    tree P a E E' δ (realizedEdge (edge34 E J) (y, t)) =
      realizedEdge (edge34 E' J) (mapParameter (CommonReferenceProduct.reanchor δ) y, t) := by
  change SSet.toTop.map (map P a E E' δ) _ = _
  rw [← realizedEdge_comp, map_edge34, edge_precomp]; rfl

/-- The same original outer reversal and four quarter clocks are retained as a whole path. -/
theorem tree_overlap (y : |parameterSSet E|) (t : I) :
    tree P a E E' δ (overlap E J (y, t)) =
      overlap E' J (mapParameter (CommonReferenceProduct.reanchor δ) y, t) := by
  change tree P a E E' δ (overlapPath E J y t) =
    overlapPath E' J (mapParameter (CommonReferenceProduct.reanchor δ) y) t
  unfold overlapPath
  apply Path.Evaluation.path_trans
  · intro s
    apply Path.Evaluation.path_symm
    intro k
    apply Path.Evaluation.path_trans
    · exact fun v ↦ tree_edge01 P a E E' δ y v
    · exact fun v ↦ tree_edge12 P a E E' δ y v
  · intro s
    apply Path.Evaluation.path_trans
    · exact fun k ↦ tree_edge03 P a E E' δ y k
    · exact fun k ↦ tree_edge34 P a E E' δ y k

/-- The whole Laurent-reference square remains literal after realization. -/
theorem tree_beta (y : FourEdgeTree.space E J) :
    SSet.toTop.map β' (tree P a E E' δ y) =
      mapParameter (CommonReferenceProduct.reanchor
        (isoWhiskerRight δ (BassProjectionPath.source P a).functor)) (SSet.toTop.map β y) := by
  change SSet.toTop.map β' (SSet.toTop.map (map P a E E' δ) y) = _
  rw [← realized_comp, beta_naturality, realized_comp]; rfl

/-- The continuous map of unreduced cones obtained by reanchoring from `E` to `E'` along `δ`. -/
def cone : C(coneSpace E J F β, coneSpace E' J F' β') :=
  (SSet.toTop.map (coneMap P a E E' δ)).hom

/-- Every original Laurent value retains its full reanchored reference. -/
theorem cone_laurent (y : |parameterSSet F|) :
    cone P a E E' δ (laurentInclusion E J F β y) =
      laurentInclusion E' J F' β' (mapParameter (CommonReferenceProduct.reanchor
        (isoWhiskerRight δ (BassProjectionPath.source P a).functor)) y) := by
  change SSet.toTop.map (coneMap P a E E' δ) (SSet.toTop.map (coneLaurent E J F β) y) = _
  rw [← realized_comp, coneMap_laurent, realized_comp]; rfl

/-- The same unreduced terminal tip is preserved. -/
theorem cone_tip : cone P a E E' δ (tip E J F β) = tip E' J F' β' := by
  change SSet.toTop.map (coneMap P a E E' δ)
    (SSet.toTop.map (coneTip E J F β) (default : |tipSSet|)) = _
  rw [← realized_comp, coneMap_tip]; rfl

/-- The original cone height stays independent of every source and overlap coordinate. -/
theorem cone_cylinder (y : FourEdgeTree.space E J) (t : I) :
    cone P a E E' δ (cylinder E J F β (y, t)) =
      cylinder E' J F' β' (tree P a E E' δ y, t) := by
  change SSet.toTop.map (coneMap P a E E' δ) (realizedEdge (coneCylinder E J F β) (y, t)) = _
  rw [← realizedEdge_comp, coneMap_cylinder, edge_precomp]; rfl

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Reanchor
