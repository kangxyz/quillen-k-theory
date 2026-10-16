/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveCompositionPrisms

/-! # Complete endpoint nodes of the two actual composition prisms

Every endpoint retains its original model morphism and the whole reference isomorphism.
The product columns and rows attach to the fixed original cube components only after these
full dependent identities; native evaluation alone is not used to identify nerve points.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeNerve
open BassReferenceMerge BassH0Merge BassH1Join
attribute [local irreducible] boundedFlatNormalizedPullback

private theorem post_reference_transport {V W T : Model.{u}} (F : V ⟶ T)
    {H : V ⟶ W} {J J' : W ⟶ T} (e : J.functor = J'.functor)
    (ρ : F.functor ≅ (H ≫ J).functor) (N : CommonReferenceNerve.Node H) :
    postReferenceNode F J' (ρ ≪≫ isoWhiskerLeft H.functor (eqToIso e)) N =
      postReferenceNode F J ρ N := by
  have h : J = J' := Model.Hom.ext e
  subst J'
  change postReferenceNode F J (ρ ≪≫ Iso.refl (H ≫ J).functor) N = _
  exact congrArg (fun τ ↦ postReferenceNode F J τ N) (Iso.trans_refl ρ)

private theorem pre_reference_transport {V W T : Model.{u}} (F : V ⟶ T)
    {H : W ⟶ T} {J J' : V ⟶ W} (e : J.functor = J'.functor)
    (ρ : F.functor ≅ (J ≫ H).functor) (N : CommonReferenceNerve.Node H) :
    preReferenceNode F J' (ρ ≪≫ isoWhiskerRight (eqToIso e) H.functor) N =
      preReferenceNode F J ρ N := by
  have h : J = J' := Model.Hom.ext e
  subst J'
  rw [eqToIso_refl, isoWhiskerRight_refl]
  change preReferenceNode F J (ρ ≪≫ Iso.refl (J ≫ H).functor) N = _
  exact congrArg (fun τ ↦ preReferenceNode F J τ N) (Iso.trans_refl ρ)

private theorem nerve_parameter_column {V W : Model.{u}} (F : V ⟶ W) {p q : ℕ}
    (N : Fin (Quillen.SimplexGrid.dimension p q + 1) → CommonReferenceNerve.Node F)
    (j : Fin (q + 1)) (z : StdSimplex ℝ (Fin (p + 1))) :
    CommonReferenceNerve.parameter F N
      (Quillen.SimplexGrid.parameter.{u} p q (z, StdSimplex.single j)) =
      CommonReferenceNerve.parameter F (fun i ↦ N (Quillen.SimplexGrid.index p q (i, j))) z :=
  (congrArg (CommonReferenceNerve.parameter F N)
    (Quillen.SimplexGrid.parameter_column.{u} p q j z)).trans
      (CommonReferenceNerve.parameter_face F N (Quillen.SimplexGrid.columnFace p q j) z)

private theorem nerve_parameter_row {V W : Model.{u}} (F : V ⟶ W) {p q : ℕ}
    (N : Fin (Quillen.SimplexGrid.dimension p q + 1) → CommonReferenceNerve.Node F)
    (i : Fin (p + 1)) (z : StdSimplex ℝ (Fin (q + 1))) :
    CommonReferenceNerve.parameter F N
      (Quillen.SimplexGrid.parameter.{u} p q (StdSimplex.single i, z)) =
      CommonReferenceNerve.parameter F (fun j ↦ N (Quillen.SimplexGrid.index p q (i, j))) z :=
  (congrArg (CommonReferenceNerve.parameter F N)
    (Quillen.SimplexGrid.parameter_row.{u} p q i z)).trans
      (CommonReferenceNerve.parameter_face F N (Quillen.SimplexGrid.rowFace p q i) z)

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- Every source-column node is the whole original right-first node, with its reference. -/
theorem laurent_prism_source_nodes (i : Fin 31) :
    laurentPrismNodes P u v w (Quillen.SimplexGrid.index 30 2 (i, 0)) =
      ModelSimplex.reanchorNodes (rightStartingAnchor P u v w)
        (BassMWhole.nodes P u (v ≫ w)) (firstIndex i) := by
  have hs := congrArg (fun N ↦ ModelSimplex.reanchorNodes (rightStartingAnchor P u v w)
    (fun _ : Fin 1 ↦ N) 0) (first_nodes P u (v ≫ w) i)
  refine (product_column_nodes _ _ _ _ _ _ _ (laurentPrismAnchor P u v w) i 0).trans ?_
  change postReferenceNode _ _ (laurentPrismAnchor P u v w ≪≫
    isoWhiskerLeft (BassH0Diagram.reference P u).functor (Iso.refl _))
    (BassH0Diagram.nodes P u i) = _
  refine (post_reference_transport _ rfl _ _).trans ?_
  unfold laurentPrismAnchor
  rw [smallIso_eqToIso]
  refine (post_reference_transport _ _ _ (BassH0Diagram.nodes P u i)).trans ?_
  simpa only [ModelSimplex.reanchorNodes, BassH1References.firstNodes,
    BassH1Components.firstNodes, postReferenceNode, Iso.trans_assoc] using hs.symm

/-- Every source-row node is the whole original left-middle node, with its reference. -/
theorem coefficient_prism_source_nodes (i : Fin 31) :
    coefficientPrismNodes P u v w (Quillen.SimplexGrid.index 2 30 (0, i)) =
      ModelSimplex.reanchorNodes (h0Anchor P (u ≫ v) w)
        (BassMWhole.nodes P (u ≫ v) w) (middleIndex i) := by
  have hs := congrArg (fun N ↦ ModelSimplex.reanchorNodes (h0Anchor P (u ≫ v) w)
    (fun _ : Fin 1 ↦ N) 0) (middle_nodes P (u ≫ v) w i)
  refine (product_row_nodes _ _ _ _ _ _ _ (coefficientPrismAnchor P u v w) 0 i).trans ?_
  change preReferenceNode _ _ (coefficientPrismAnchor P u v w ≪≫
    isoWhiskerRight (Iso.refl _) (BassH0Diagram.reference P w).functor)
    (BassH0Diagram.nodes P w i) = _
  refine (pre_reference_transport _ rfl _ _).trans ?_
  unfold coefficientPrismAnchor
  rw [smallIso_eqToIso]
  refine (pre_reference_transport _ _ _ (BassH0Diagram.nodes P w i)).trans ?_
  simpa only [ModelSimplex.reanchorNodes, BassH1References.middleNodes,
    BassH1Components.middleNodes, preReferenceNode, Iso.trans_assoc] using hs.symm

/-- The Laurent product target anchor is the exact original post-first anchor. -/
theorem laurent_prism_target_anchor :
    laurentPrismAnchor P u v w ≪≫ isoWhiskerLeft (BassH0Diagram.reference P u).functor
      (BinaryNormalizationSimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map w))
        (coefficientMap P ((laurentUnderFunctor R).map v))) =
      postcompAnchor P u v w ≪≫ isoWhiskerRight (BassH1References.firstIso P u v)
        (coefficientModel P ((laurentUnderFunctor R).map w)).functor := by
  have hS : isoWhiskerLeft (BassH0Diagram.reference P u).functor
      (laurentCompositionIso P v w) ≪≫
      (Functor.associator (BassH0Diagram.reference P u).functor
        (coefficientModel P ((laurentUnderFunctor R).map v)).functor
        (coefficientModel P ((laurentUnderFunctor R).map w)).functor).symm =
      isoWhiskerLeft (BassH0Diagram.reference P u).functor
        (laurentCompositionIso P v w) := by
    change _ ≪≫ Iso.refl _ = _
    exact Iso.trans_refl _
  have h := (congrArg (fun e ↦ (rightStartingAnchor P u v w ≪≫
    BassH1References.firstIso P u (v ≫ w)) ≪≫ e) hS).symm.trans
      (right_first_composition_anchor P u v w)
  have hk : laurentCompositionIso P v w =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        (laurentComposition_total P v w))) ≪≫
        BinaryNormalizationSimplex.total
          (coefficientMap P ((laurentUnderFunctor R).map w))
          (coefficientMap P ((laurentUnderFunctor R).map v)) := smallIso_trans _ _
  refine Eq.trans ?_ h
  rw [hk, isoWhiskerLeft_trans]
  exact Iso.trans_assoc _ _ _

/-- The coefficient product target anchor is the exact original pre-middle anchor. -/
theorem coefficient_prism_target_anchor :
    coefficientPrismAnchor P u v w ≪≫ isoWhiskerRight
      (BinaryNormalizationSimplex.total (coefficientMap P v) (coefficientMap P u))
      (BassH0Diagram.reference P w).functor =
      precompAnchor P u v w ≪≫ isoWhiskerLeft (coefficientModel P u).functor
        (BassH1References.middleIso P v w) := by
  have hS : isoWhiskerRight (coefficientCompositionIso P u v)
      (BassH0Diagram.reference P w).functor ≪≫
      Functor.associator (coefficientModel P u).functor (coefficientModel P v).functor
        (BassH0Diagram.reference P w).functor =
      isoWhiskerRight (coefficientCompositionIso P u v)
        (BassH0Diagram.reference P w).functor := by
    change _ ≪≫ Iso.refl _ = _
    exact Iso.trans_refl _
  have h := (congrArg (fun e ↦ (h0Anchor P (u ≫ v) w ≪≫
    BassH1References.middleIso P (u ≫ v) w) ≪≫ e) hS).symm.trans
      (left_middle_composition_anchor P u v w)
  have hk : coefficientCompositionIso P u v =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        (coefficientMap_comp P u v))) ≪≫
        BinaryNormalizationSimplex.total (coefficientMap P v) (coefficientMap P u) :=
    smallIso_trans _ _
  refine Eq.trans ?_ h
  rw [hk, isoWhiskerRight_trans]
  exact Iso.trans_assoc _ _ _

/-- All 31 target-column nodes are the complete original post-first component. -/
theorem laurent_prism_target_nodes (i : Fin 31) :
    laurentPrismNodes P u v w (Quillen.SimplexGrid.index 30 2 (i, 2)) =
      postcompNodes P u v w (firstIndex i) := by
  have ht := reanchor_postcomp_nodes
    (coefficientModel P ((laurentUnderFunctor R).map w)) (postcompAnchor P u v w)
    (BassH1References.firstIso P u v) _ _ firstIndex (first_nodes P u v) i
  refine (product_column_nodes _ _ _ _ _ _ _ (laurentPrismAnchor P u v w) i 2).trans ?_
  change postReferenceNode _ _ (laurentPrismAnchor P u v w ≪≫
    isoWhiskerLeft (BassH0Diagram.reference P u).functor
      (BinaryNormalizationSimplex.total _ _)) (BassH0Diagram.nodes P u i) = _
  rw [laurent_prism_target_anchor]
  exact Eq.trans (by rfl) ht.symm

/-- All 31 target-row nodes are the complete original pre-middle component. -/
theorem coefficient_prism_target_nodes (i : Fin 31) :
    coefficientPrismNodes P u v w (Quillen.SimplexGrid.index 2 30 (2, i)) =
      precompNodes P u v w (middleIndex i) := by
  have ht := reanchor_precomp_nodes (coefficientModel P u) (precompAnchor P u v w)
    (BassH1References.middleIso P v w) _ _ middleIndex (middle_nodes P v w) i
  refine (product_row_nodes _ _ _ _ _ _ _ (coefficientPrismAnchor P u v w) 2 i).trans ?_
  change preReferenceNode _ _ (coefficientPrismAnchor P u v w ≪≫
    isoWhiskerRight (BinaryNormalizationSimplex.total _ _)
      (BassH0Diagram.reference P w).functor) (BassH0Diagram.nodes P w i) = _
  rw [coefficient_prism_target_anchor]
  exact Eq.trans (by rfl) ht.symm

universe v
private theorem first_component_parameter {V W : Model.{v}} (F : V ⟶ W)
    (N : Fin 140 → CommonReferenceNerve.Node F) (s t : unitInterval) :
    CommonReferenceNerve.parameter F N (BassMWhole.scalarCube.{u} ![1, lower s, t]) =
      CommonReferenceNerve.parameter F (fun i ↦ N (firstIndex i))
        (BassH0Diagram.parameter (s, t)) := by
  rw [BassMWhole.cube_one]
  change CommonReferenceNerve.parameter F N
    (StdSimplex.map BassMWholeOrder.oldIndex (BassH1Order.h1Parameter.{u} (lower s, t))) = _
  rw [BassH1Order.h1_lower]
  change CommonReferenceNerve.parameter F N
    (StdSimplex.map BassMWholeOrder.oldIndex
      (StdSimplex.map BassH1Order.firstIndex (BassH0Diagram.parameter (s, t)))) = _
  rw [← StdSimplex.map_comp]
  exact h0_supported_parameter F N _ firstIndex (fun _ ↦ rfl)
    BassMWholeOrder.oldFirstPlus_monotone BassMWholeOrder.oldFirstMinus_monotone s t

private theorem middle_component_parameter {V W : Model.{v}} (F : V ⟶ W)
    (N : Fin 140 → CommonReferenceNerve.Node F) (s t : unitInterval) :
    CommonReferenceNerve.parameter F N
      (BassMWhole.scalarCube.{u} ![1, upper s, upper (lower t)]) =
      CommonReferenceNerve.parameter F (fun i ↦ N (middleIndex i))
        (BassH0Diagram.parameter (s, t)) := by
  rw [BassMWhole.cube_one]
  change CommonReferenceNerve.parameter F N
    (StdSimplex.map BassMWholeOrder.oldIndex
      (BassH1Order.h1Parameter.{u} (upper s, upper (lower t)))) = _
  rw [BassH1Order.h1_middle_cell]
  change CommonReferenceNerve.parameter F N
    (StdSimplex.map BassMWholeOrder.oldIndex
      (StdSimplex.map BassH1Order.middleIndex (BassH0Diagram.parameter (s, t)))) = _
  rw [← StdSimplex.map_comp]
  exact h0_supported_parameter F N _ middleIndex (fun _ ↦ rfl)
    BassMWholeOrder.oldMiddlePlus_monotone BassMWholeOrder.oldMiddleMinus_monotone s t

/-- The entire source of the Laurent prism is the unchanged right-first cube component. -/
theorem laurent_prism_source_face (s t : unitInterval) :
    laurentPrism P u v w ![0, s, t] =
      cubeLift P u (v ≫ w) (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (rightStartingAnchor P u v w) ![1, lower s, t] := by
  change CommonReferenceNerve.parameter _ (laurentPrismNodes P u v w)
    (Quillen.SimplexGrid.parameter.{u + 1} 30 2
      (BassH0Diagram.parameter (s, t), binaryPath (k := 2) 0 1 2 0)) = _
  rw [Path.source]
  refine (nerve_parameter_column _ _ _ _).trans ?_
  change CommonReferenceNerve.parameter _
    (fun i ↦ laurentPrismNodes P u v w (Quillen.SimplexGrid.index 30 2 (i, 0))) _ = _
  rw [funext (laurent_prism_source_nodes P u v w)]
  exact (first_component_parameter _ _ s t).symm

/-- The entire target of the Laurent prism is the unchanged post-first cube component. -/
theorem laurent_prism_target_face (s t : unitInterval) :
    laurentPrism P u v w ![1, s, t] = postcompLift P u v w ![1, lower s, t] := by
  change CommonReferenceNerve.parameter _ (laurentPrismNodes P u v w)
    (Quillen.SimplexGrid.parameter.{u + 1} 30 2
      (BassH0Diagram.parameter (s, t), binaryPath (k := 2) 0 1 2 1)) = _
  rw [Path.target]
  refine (nerve_parameter_column _ _ _ _).trans ?_
  change CommonReferenceNerve.parameter _
    (fun i ↦ laurentPrismNodes P u v w (Quillen.SimplexGrid.index 30 2 (i, 2))) _ = _
  rw [funext (laurent_prism_target_nodes P u v w)]
  exact (first_component_parameter _ _ s t).symm

/-- The entire coefficient-prism source is the unchanged left-middle quarter-speed component. -/
theorem coefficient_prism_source_face (s t : unitInterval) :
    coefficientPrism P u v w ![0, s, t] =
      cubeLift P (u ≫ v) w (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (h0Anchor P (u ≫ v) w) ![1, upper s, upper (lower t)] := by
  change CommonReferenceNerve.parameter _ (coefficientPrismNodes P u v w)
    (Quillen.SimplexGrid.parameter.{u + 1} 2 30
      (binaryPath (k := 2) 0 1 2 0, BassH0Diagram.parameter (s, t))) = _
  rw [Path.source]
  refine (nerve_parameter_row _ _ _ _).trans ?_
  change CommonReferenceNerve.parameter _
    (fun i ↦ coefficientPrismNodes P u v w (Quillen.SimplexGrid.index 2 30 (0, i))) _ = _
  rw [funext (coefficient_prism_source_nodes P u v w)]
  exact (middle_component_parameter _ _ s t).symm

/-- The entire coefficient-prism target is the unchanged pre-middle quarter-speed component. -/
theorem coefficient_prism_target_face (s t : unitInterval) :
    coefficientPrism P u v w ![1, s, t] =
      precompLift P u v w ![1, upper s, upper (lower t)] := by
  change CommonReferenceNerve.parameter _ (coefficientPrismNodes P u v w)
    (Quillen.SimplexGrid.parameter.{u + 1} 2 30
      (binaryPath (k := 2) 0 1 2 1, BassH0Diagram.parameter (s, t))) = _
  rw [Path.target]
  refine (nerve_parameter_row _ _ _ _).trans ?_
  change CommonReferenceNerve.parameter _
    (fun i ↦ coefficientPrismNodes P u v w (Quillen.SimplexGrid.index 2 30 (2, i))) _ = _
  rw [funext (coefficient_prism_target_nodes P u v w)]
  exact (middle_component_parameter _ _ s t).symm

end Quillen.PerfectComplexes.BassMWholeNerve
