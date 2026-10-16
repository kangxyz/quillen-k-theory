/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveWhiskered

/-!
# Exact starting attachments of the two original whiskered Bass cubes

The two specified H1 component faces retain their complete dependent nodes, canonical reference
isomorphisms, and original half/quarter coordinate speeds. The actual nerve equalities use only
the six original H0 primitive supports. Other faces and cone reassociation are separate.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeNerve
open BassReferenceMerge
attribute [local irreducible] boundedFlatNormalizedPullback

/-- Equality in the second geometric factor retains the specified anchored comparison. -/
theorem anchored_target_transport {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    {g g' : Y ⟶ Z} (e : g = g') (k : X ⟶ Z)
    (h : k = f ≫ g) (h' : k = f ≫ g') :
    (eqToIso (congrArg boundedFlatNormalizedPullback h) ≪≫
      boundedFlatNormalizedPullbackCompIso f g) ≪≫
        isoWhiskerRight (eqToIso (congrArg boundedFlatNormalizedPullback e))
          (boundedFlatNormalizedPullback f) =
      eqToIso (congrArg boundedFlatNormalizedPullback h') ≪≫
        boundedFlatNormalizedPullbackCompIso f g' := by
  subst g'
  simp only [eqToIso_refl, isoWhiskerRight_refl, Iso.trans_refl]

/-- Equality in the first geometric factor retains the specified anchored comparison. -/
theorem anchored_source_transport {X Y Z : Scheme.{u}} {f f' : X ⟶ Y}
    (e : f = f') (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : k = f ≫ g) (h' : k = f' ≫ g) :
    (eqToIso (congrArg boundedFlatNormalizedPullback h) ≪≫
      boundedFlatNormalizedPullbackCompIso f g) ≪≫
        isoWhiskerLeft (boundedFlatNormalizedPullback g)
          (eqToIso (congrArg boundedFlatNormalizedPullback e)) =
      eqToIso (congrArg boundedFlatNormalizedPullback h') ≪≫
        boundedFlatNormalizedPullbackCompIso f' g := by
  subst f'
  simp only [eqToIso_refl, isoWhiskerLeft_refl, Iso.trans_refl]

variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The existing H0 reference equality is precisely its original small-functor transport. -/
theorem h0_reference_small {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c) :
    eqToIso (BassH0Merge.reference_eq P u v) =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (BassH0Merge.total P u v).symm)) :=
  (smallIso_eqToIso _).symm

/-- The inverse H0 anchor uses the forward geometric equality, without concrete expansion. -/
theorem h0_anchor_small {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c) :
    h0Anchor P u v =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (BassH0Merge.total P u v))) := by
  unfold h0Anchor
  rw [h0_reference_small]
  apply Iso.ext
  rfl

/-- The actual coefficient model has exactly the original small normalized pullback functor. -/
theorem coefficient_model_functor {a b : Under R} (u : a ⟶ b) :
    (coefficientModel P u).functor =
      AsSmall.down ⋙ boundedFlatNormalizedPullback (coefficientMap P u) ⋙ AsSmall.up := rfl

variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- The geometric postcomposition anchor is its displayed original small comparison. -/
theorem postcomp_anchor_small : postcompAnchor P u v w =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (postcomp_total P u v w)) ≪≫
      boundedFlatNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map w))
        (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)) := rfl

/-- The geometric precomposition anchor is its displayed original small comparison. -/
theorem precomp_anchor_small : precompAnchor P u v w =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (precomp_total P u v w)) ≪≫
      boundedFlatNormalizedPullbackCompIso
        (laurentProjection P d ≫ coefficientMap P w ≫ coefficientMap P v)
        (coefficientMap P u)) := rfl

/-- Outer association is transported through the same actual geometric total and small functors. -/
theorem starting_assoc_small :
    eqToIso (congrArg (fun z ↦ (BassH0Diagram.reference P z).functor) (Category.assoc u v w)) =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        (congrArg (fun z ↦ coefficientMap P ((laurentUnderFunctor R).map z) ≫
          laurentProjection P a) (Category.assoc u v w)))) :=
  (smallIso_eqToIso _).symm

/-- The postcomposed H0 attachment has exactly the original first-component anchor. -/
theorem postcomp_start_anchor :
    h0Anchor P (u ≫ v) w ≪≫ BassH1References.firstIso P (u ≫ v) w =
      postcompAnchor P u v w ≪≫ isoWhiskerRight
        (eqToIso (BassH0Merge.reference_eq P u v))
        (coefficientModel P ((laurentUnderFunctor R).map w)).functor := by
  rw [h0_anchor_small, BassH1References.firstIso, postcomp_anchor_small, h0_reference_small]
  erw [smallIso_postcomp, ← smallIso_trans, ← smallIso_trans]
  apply congrArg smallIso
  rw [← Iso.trans_assoc, eqToIso_trans]
  exact (anchored_target_transport
    (coefficientMap P ((laurentUnderFunctor R).map w)) (BassH0Merge.total P u v).symm
    _ (postcomp_total P u v w)
    ((BassH0Merge.total P (u ≫ v) w).trans
      (BassH1References.first_total P (u ≫ v) w).symm)).symm

/-- On the actual coefficient arrows, the displayed associativity transport is the identity.
The original rightStartingAnchor definition still retains that specified transport. -/
theorem right_starting_anchor_h0 : rightStartingAnchor P u v w = h0Anchor P u (v ≫ w) := by
  change Iso.refl _ ≪≫ h0Anchor P u (v ≫ w) = _
  exact Iso.refl_trans _

/-- The source-whiskered H0 attachment retains the actual associativity transport and anchor. -/
theorem precomp_start_anchor :
    rightStartingAnchor P u v w ≪≫ BassH1References.middleIso P u (v ≫ w) =
      precompAnchor P u v w ≪≫ isoWhiskerLeft (coefficientModel P u).functor
        (eqToIso (BassH0Merge.reference_eq P v w)) := by
  rw [right_starting_anchor_h0, h0_anchor_small,
    BassH1References.middleIso, precomp_anchor_small, h0_reference_small]
  erw [smallIso_precomp, ← smallIso_trans, ← smallIso_trans]
  apply congrArg smallIso
  rw [← Iso.trans_assoc, eqToIso_trans]
  exact (anchored_source_transport (BassH0Merge.total P v w).symm (coefficientMap P u)
    _ (precomp_total P u v w)
    ((congrArg (fun z ↦ coefficientMap P ((laurentUnderFunctor R).map z) ≫
      laurentProjection P a) (Category.assoc u v w)).trans
      ((BassH0Merge.total P u (v ≫ w)).trans
        (BassH1References.middle_total P u (v ≫ w)).symm))).symm

/-- Postcomposition preserves both the full node and the specified composed reference. -/
theorem reanchor_postcomp_nodes {V W T : Model.{u}} (J : W ⟶ T)
    {F : V ⟶ T} {G H : V ⟶ W} {k l : ℕ}
    (e : F.functor ≅ (G ≫ J).functor) (e' : G.functor ≅ H.functor)
    (N : Fin (k + 1) → CommonReferenceNerve.Node G)
    (M : Fin (l + 1) → CommonReferenceNerve.Node H) (f : Fin (l + 1) → Fin (k + 1))
    (h : ∀ i, N (f i) = ModelSimplex.reanchorNodes e' M i) (i : Fin (l + 1)) :
    ModelSimplex.reanchorNodes e (fun j ↦ CommonReferenceNerve.postcompNode J (N j)) (f i) =
      ModelSimplex.reanchorNodes (e ≪≫ isoWhiskerRight e' J.functor)
        (fun j ↦ CommonReferenceNerve.postcompNode J (M j)) i := by
  change (⟨(N (f i)).1 ≫ J, e ≪≫ isoWhiskerRight (N (f i)).2 J.functor⟩ :
    CommonReferenceNerve.Node F) = _
  rw [h i]
  simp only [ModelSimplex.reanchorNodes, CommonReferenceNerve.postcompNode,
    isoWhiskerRight_trans, Iso.trans_assoc]

/-- Precomposition likewise preserves the specified full reference composite. -/
theorem reanchor_precomp_nodes {V W T : Model.{u}} (J : V ⟶ W)
    {F : V ⟶ T} {G H : W ⟶ T} {k l : ℕ}
    (e : F.functor ≅ (J ≫ G).functor) (e' : G.functor ≅ H.functor)
    (N : Fin (k + 1) → CommonReferenceNerve.Node G)
    (M : Fin (l + 1) → CommonReferenceNerve.Node H) (f : Fin (l + 1) → Fin (k + 1))
    (h : ∀ i, N (f i) = ModelSimplex.reanchorNodes e' M i) (i : Fin (l + 1)) :
    ModelSimplex.reanchorNodes e (fun j ↦ CommonReferenceNerve.precompNode J (N j)) (f i) =
      ModelSimplex.reanchorNodes (e ≪≫ isoWhiskerLeft J.functor e')
        (fun j ↦ CommonReferenceNerve.precompNode J (M j)) i := by
  change (⟨J ≫ (N (f i)).1, e ≪≫ isoWhiskerLeft J.functor (N (f i)).2⟩ :
    CommonReferenceNerve.Node F) = _
  rw [h i]
  simp only [ModelSimplex.reanchorNodes, CommonReferenceNerve.precompNode,
    isoWhiskerLeft_trans, Iso.trans_assoc]

/-- The original first component's enclosing labels, only restricted supports are ordered. -/
def firstIndex : Fin 31 → Fin 140 := BassMWholeOrder.oldIndex ∘ BassH1Order.firstIndex

/-- The original middle component has its distinct enclosing labels. -/
def middleIndex : Fin 31 → Fin 140 := BassMWholeOrder.oldIndex ∘ BassH1Order.middleIndex

/-- Every full first-component node survives the original 140-node assembly. -/
theorem first_nodes {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c) (i : Fin 31) :
    BassMWhole.nodes P u v (firstIndex i) = BassH1References.firstNodes P u v i := by
  unfold firstIndex
  rw [Function.comp_apply, BassMWhole.old_nodes, BassH1Merged.first_nodes]

/-- Every full middle-component node survives the same original assembly. -/
theorem middle_nodes {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c) (i : Fin 31) :
    BassMWhole.nodes P u v (middleIndex i) = BassH1References.middleNodes P u v i := by
  unfold middleIndex
  rw [Function.comp_apply, BassMWhole.old_nodes, BassH1Merged.middle_nodes]

/-- All 31 postcomposed H0 nodes are exactly the outer cube's original first-component nodes. -/
theorem postcomp_start_nodes (i : Fin 31) :
    postcompNodes P u v w (h0Index i) =
      ModelSimplex.reanchorNodes (h0Anchor P (u ≫ v) w)
        (BassH1References.firstNodes P (u ≫ v) w) i := by
  unfold postcompNodes
  rw [reanchor_postcomp_nodes _ _ _ _ _ h0Index (h0_nodes P u v) i,
    ← postcomp_start_anchor]
  simp only [ModelSimplex.reanchorNodes, CommonReferenceNerve.postcompNode,
    BassH1References.firstNodes, BassH1Components.firstNodes, Iso.trans_assoc]
  rfl

/-- All 31 precomposed H0 nodes are exactly the outer cube's original middle-component nodes. -/
theorem precomp_start_nodes (i : Fin 31) :
    precompNodes P u v w (h0Index i) =
      ModelSimplex.reanchorNodes (rightStartingAnchor P u v w)
        (BassH1References.middleNodes P u (v ≫ w)) i := by
  unfold precompNodes
  rw [reanchor_precomp_nodes _ _ _ _ _ h0Index (h0_nodes P v w) i,
    ← precomp_start_anchor]
  simp only [ModelSimplex.reanchorNodes, CommonReferenceNerve.precompNode,
    BassH1References.middleNodes, BassH1Components.middleNodes, Iso.trans_assoc]
  rfl

/-- A whole H0 parameter uses precisely its six ordered primitive supports. -/
theorem h0_supported_parameter {V W : Model.{u}} (F : V ⟶ W) {k : ℕ}
    (N : Fin (k + 1) → CommonReferenceNerve.Node F)
    (M : Fin 31 → CommonReferenceNerve.Node F) (f : Fin 31 → Fin (k + 1))
    (h : ∀ i, N (f i) = M i)
    (hp : ∀ i : Fin 3, Monotone (f ∘
      (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.plusFace).toOrderHom))
    (hm : ∀ i : Fin 3, Monotone (f ∘
      (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.minusFace).toOrderHom))
    (s t : unitInterval) :
    CommonReferenceNerve.parameter F N (StdSimplex.map f (BassH0Diagram.parameter (s, t))) =
      CommonReferenceNerve.parameter F M (BassH0Diagram.parameter (s, t)) := by
  obtain ⟨α, hα, i, z, hz⟩ := BassPrimitiveSupport.h0_support (s, t)
  change StdSimplex.map (BassPrimitiveSupport.rectangleFace i ≫ α).toOrderHom z =
    BassH0Diagram.parameter (s, t) at hz
  have ho : Monotone (f ∘ (BassPrimitiveSupport.rectangleFace i ≫ α).toOrderHom) := by
    rcases Set.mem_insert_iff.mp hα with hα | hα
    · subst α
      exact hp i
    · have hα := Set.mem_singleton_iff.mp hα
      subst α
      exact hm i
  rw [← hz]
  exact CommonReferenceNerve.parameter_supported F M N f h
    (BassPrimitiveSupport.rectangleFace i ≫ α) ho z

/-- The entire original postcomposed cube starts on the specified half-speed H1 component. -/
theorem postcomp_start_face (s t : unitInterval) :
    cubeLift P (u ≫ v) w (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (h0Anchor P (u ≫ v) w) ![1, lower s, t] =
      postcompLift P u v w ![0, s, t] := by
  change CommonReferenceNerve.parameter _
    (ModelSimplex.reanchorNodes (h0Anchor P (u ≫ v) w) (BassMWhole.nodes P (u ≫ v) w))
    (BassMWhole.scalarCube.{u} ![1, lower s, t]) =
      CommonReferenceNerve.parameter _ (postcompNodes P u v w)
        (BassMWhole.scalarCube.{u} ![0, s, t])
  rw [BassMWhole.cube_one, BassMWhole.cube_zero, h0_parameter_scalar]
  change CommonReferenceNerve.parameter _ _
    (StdSimplex.map BassMWholeOrder.oldIndex (BassH1Order.h1Parameter.{u} (lower s, t))) = _
  rw [BassH1Order.h1_lower]
  change CommonReferenceNerve.parameter _ _
    (StdSimplex.map BassMWholeOrder.oldIndex
      (StdSimplex.map BassH1Order.firstIndex (BassH0Diagram.parameter (s, t)))) = _
  rw [← StdSimplex.map_comp]
  trans CommonReferenceNerve.parameter _
    (ModelSimplex.reanchorNodes (h0Anchor P (u ≫ v) w)
      (BassH1References.firstNodes P (u ≫ v) w)) (BassH0Diagram.parameter (s, t))
  · exact h0_supported_parameter _ _ _ firstIndex
      (fun i ↦ congrArg (fun N ↦ (⟨N.1, h0Anchor P (u ≫ v) w ≪≫ N.2⟩ :
        CommonReferenceNerve.Node (BassH0Diagram.reference P ((u ≫ v) ≫ w))))
        (first_nodes P (u ≫ v) w i))
      BassMWholeOrder.oldFirstPlus_monotone BassMWholeOrder.oldFirstMinus_monotone s t
  · exact (h0_supported_parameter _ _ _ h0Index (postcomp_start_nodes P u v w)
      BassMWholeOrder.oldH0Plus_monotone BassMWholeOrder.oldH0Minus_monotone s t).symm

/-- The entire original precomposed cube starts on the unchanged middle-quarter H1 component. -/
theorem precomp_start_face (s t : unitInterval) :
    cubeLift P u (v ≫ w) (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (rightStartingAnchor P u v w) ![1, upper s, upper (lower t)] =
      precompLift P u v w ![0, s, t] := by
  change CommonReferenceNerve.parameter _
    (ModelSimplex.reanchorNodes (rightStartingAnchor P u v w) (BassMWhole.nodes P u (v ≫ w)))
    (BassMWhole.scalarCube.{u} ![1, upper s, upper (lower t)]) =
      CommonReferenceNerve.parameter _ (precompNodes P u v w)
        (BassMWhole.scalarCube.{u} ![0, s, t])
  rw [BassMWhole.cube_one, BassMWhole.cube_zero, h0_parameter_scalar]
  change CommonReferenceNerve.parameter _ _
    (StdSimplex.map BassMWholeOrder.oldIndex
      (BassH1Order.h1Parameter.{u} (upper s, upper (lower t)))) = _
  rw [BassH1Order.h1_middle_cell]
  change CommonReferenceNerve.parameter _ _
    (StdSimplex.map BassMWholeOrder.oldIndex
      (StdSimplex.map BassH1Order.middleIndex (BassH0Diagram.parameter (s, t)))) = _
  rw [← StdSimplex.map_comp]
  trans CommonReferenceNerve.parameter _
    (ModelSimplex.reanchorNodes (rightStartingAnchor P u v w)
      (BassH1References.middleNodes P u (v ≫ w))) (BassH0Diagram.parameter (s, t))
  · exact h0_supported_parameter _ _ _ middleIndex
      (fun i ↦ congrArg (fun N ↦ (⟨N.1, rightStartingAnchor P u v w ≪≫ N.2⟩ :
        CommonReferenceNerve.Node (BassH0Diagram.reference P ((u ≫ v) ≫ w))))
        (middle_nodes P u (v ≫ w) i))
      BassMWholeOrder.oldMiddlePlus_monotone BassMWholeOrder.oldMiddleMinus_monotone s t
  · exact (h0_supported_parameter _ _ _ h0Index (precomp_start_nodes P u v w)
      BassMWholeOrder.oldH0Plus_monotone BassMWholeOrder.oldH0Minus_monotone s t).symm

end Quillen.PerfectComplexes.BassMWholeNerve
