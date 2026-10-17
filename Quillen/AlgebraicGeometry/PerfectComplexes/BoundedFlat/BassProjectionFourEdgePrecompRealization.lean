/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgePrecompCone
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeExt
public import Quillen.Topology.Path.NullWordEvaluation

/-! Every original tree edge and cone coordinate survives full source precomposition. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Precomp
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
variable {U V : Model.{u + 1}} (A : U ⟶ V)
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "J" => normalizedMap (polynomialProjection P a)
local notation "F" => reference P a E
local notation "F'" => reference P a (A ≫ E)
local notation "β" => beta P a E
local notation "β'" => beta P a (A ≫ E)

/-- The continuous four-edge tree map induced by source precomposition with `A`. -/
def tree : C(FourEdgeTree.space E J, FourEdgeTree.space (A ≫ E) J) :=
  (SSet.toTop.map (map P a A E)).hom

theorem tree_plus (y : |parameterSSet (E ≫ J)|) :
    tree P a A E (SSet.toTop.map (plusVertex E J) y) =
      SSet.toTop.map (plusVertex (A ≫ E) J) (mapParameter (precompNode A) y) := by
  change SSet.toTop.map (map P a A E) _ = _
  rw [← realized_comp, map_plus, realized_comp]; rfl

theorem tree_minus (y : |parameterSSet (E ≫ J)|) :
    tree P a A E (SSet.toTop.map (minusVertex E J) y) =
      SSet.toTop.map (minusVertex (A ≫ E) J) (mapParameter (precompNode A) y) := by
  change SSet.toTop.map (map P a A E) _ = _
  rw [← realized_comp, map_minus, realized_comp]; rfl

theorem tree_edge12 (y : |parameterSSet E|) (t : I) :
    tree P a A E (realizedEdge (edge12 E J) (y, t)) =
      realizedEdge (edge12 (A ≫ E) J) (mapParameter (precompNode A) y, t) := by
  change SSet.toTop.map (map P a A E) _ = _
  rw [← realizedEdge_comp, map_edge12, edge_precomp]; rfl

theorem tree_edge01 (y : |parameterSSet E|) (t : I) :
    tree P a A E (realizedEdge (edge01 E J) (y, t)) =
      realizedEdge (edge01 (A ≫ E) J) (mapParameter (precompNode A) y, t) := by
  change SSet.toTop.map (map P a A E) _ = _
  rw [← realizedEdge_comp, map_edge01, edge_precomp]; rfl

theorem tree_edge03 (y : |parameterSSet E|) (t : I) :
    tree P a A E (realizedEdge (edge03 E J) (y, t)) =
      realizedEdge (edge03 (A ≫ E) J) (mapParameter (precompNode A) y, t) := by
  change SSet.toTop.map (map P a A E) _ = _
  rw [← realizedEdge_comp, map_edge03, edge_precomp]; rfl

theorem tree_edge34 (y : |parameterSSet E|) (t : I) :
    tree P a A E (realizedEdge (edge34 E J) (y, t)) =
      realizedEdge (edge34 (A ≫ E) J) (mapParameter (precompNode A) y, t) := by
  change SSet.toTop.map (map P a A E) _ = _
  rw [← realizedEdge_comp, map_edge34, edge_precomp]; rfl

/-- The same original outer reversal and four quarter clocks are retained as a whole path. -/
theorem tree_overlap (y : |parameterSSet E|) (t : I) :
    tree P a A E (overlap E J (y, t)) =
      overlap (A ≫ E) J (mapParameter (precompNode A) y, t) := by
  change tree P a A E (overlapPath E J y t) =
    overlapPath (A ≫ E) J (mapParameter (precompNode A) y) t
  unfold overlapPath
  apply Path.Evaluation.path_trans
  · intro s
    apply Path.Evaluation.path_symm
    intro k
    apply Path.Evaluation.path_trans
    · exact fun v ↦ tree_edge01 P a A E y v
    · exact fun v ↦ tree_edge12 P a A E y v
  · intro s
    apply Path.Evaluation.path_trans
    · exact fun k ↦ tree_edge03 P a A E y k
    · exact fun k ↦ tree_edge34 P a A E y k

/-- The whole Laurent-reference square remains literal after realization. -/
theorem tree_beta (y : FourEdgeTree.space E J) :
    SSet.toTop.map β' (tree P a A E y) =
      mapParameter (precompNode A) (SSet.toTop.map β y) := by
  change SSet.toTop.map β' (SSet.toTop.map (map P a A E) y) = _
  rw [← realized_comp, beta_naturality, realized_comp]; rfl

/-- The continuous map of unreduced cones induced by source precomposition with `A`. -/
def cone : C(coneSpace E J F β, coneSpace (A ≫ E) J F' β') :=
  (SSet.toTop.map (coneMap P a A E)).hom

/-- Every original Laurent value retains its full precomposed reference. -/
theorem cone_laurent (y : |parameterSSet F|) :
    cone P a A E (laurentInclusion E J F β y) =
      laurentInclusion (A ≫ E) J F' β' (mapParameter (precompNode A) y) := by
  change SSet.toTop.map (coneMap P a A E) (SSet.toTop.map (coneLaurent E J F β) y) = _
  rw [← realized_comp, coneMap_laurent, realized_comp]; rfl

/-- The same unreduced terminal tip is preserved. -/
theorem cone_tip : cone P a A E (tip E J F β) = tip (A ≫ E) J F' β' := by
  change SSet.toTop.map (coneMap P a A E)
    (SSet.toTop.map (coneTip E J F β) (default : |tipSSet|)) = _
  rw [← realized_comp, coneMap_tip]; rfl

/-- The original cone height stays independent of every source and overlap coordinate. -/
theorem cone_cylinder (y : FourEdgeTree.space E J) (t : I) :
    cone P a A E (cylinder E J F β (y, t)) =
      cylinder (A ≫ E) J F' β' (tree P a A E y, t) := by
  change SSet.toTop.map (coneMap P a A E) (realizedEdge (coneCylinder E J F β) (y, t)) = _
  rw [← realizedEdge_comp, coneMap_cylinder, edge_precomp]; rfl

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Precomp
