/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveWhiskeredTerminal

/-!
# Exact canonical references for the two distinct terminal components

The coefficient and Laurent comparison isomorphisms retain their original geometric
transports. The base-anchor identities include the specified associators. Full nodewise
comparisons retain the distinct endpoint nodes; no composition prism is constructed here.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMWholeNerve
open BassReferenceMerge
attribute [local irreducible] boundedFlatNormalizedPullback

variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The original coefficient composition comparison, with its actual equality transport. -/
def coefficientCompositionIso {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c) :
    (coefficientModel P (u ≫ v)).functor ≅
      (coefficientModel P u ≫ coefficientModel P v).functor :=
  smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (coefficientMap_comp P u v)) ≪≫
    boundedFlatNormalizedPullbackCompIso (coefficientMap P v) (coefficientMap P u))

/-- Laurent composition keeps the actual Laurent functor's composite-arrow transport. -/
theorem laurentComposition_total {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c) :
    coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)) =
      coefficientMap P ((laurentUnderFunctor R).map v) ≫
        coefficientMap P ((laurentUnderFunctor R).map u) :=
  (congrArg (coefficientMap P) ((laurentUnderFunctor R).map_comp u v)).trans
    (coefficientMap_comp P _ _)

/-- The Laurent comparison starts at the literal Laurent image of the composite arrow. -/
def laurentCompositionIso {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c) :
    (coefficientModel P ((laurentUnderFunctor R).map (u ≫ v))).functor ≅
      (coefficientModel P ((laurentUnderFunctor R).map u) ≫
        coefficientModel P ((laurentUnderFunctor R).map v)).functor :=
  smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      (laurentComposition_total P u v)) ≪≫
    boundedFlatNormalizedPullbackCompIso
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u)))

variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- The right-first raw total retains the actual H0(u) geometric reference. -/
theorem right_first_total :
    coefficientMap P ((laurentUnderFunctor R).map ((u ≫ v) ≫ w)) ≫ laurentProjection P a =
      coefficientMap P ((laurentUnderFunctor R).map (v ≫ w)) ≫
        (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a) :=
  (congrArg (fun z ↦ coefficientMap P ((laurentUnderFunctor R).map z) ≫
    laurentProjection P a) (Category.assoc u v w)).trans
      ((BassH0Merge.total P u (v ≫ w)).trans
        (BassH1References.first_total P u (v ≫ w)).symm)

/-- The left-middle raw total retains the actual H0(w) geometric reference. -/
theorem left_middle_total :
    coefficientMap P ((laurentUnderFunctor R).map ((u ≫ v) ≫ w)) ≫ laurentProjection P a =
      (coefficientMap P ((laurentUnderFunctor R).map w) ≫ laurentProjection P c) ≫
        coefficientMap P (u ≫ v) :=
  (BassH0Merge.total P (u ≫ v) w).trans
    (BassH1References.middle_total P (u ≫ v) w).symm

/-- The right-first anchor exposes only its original raw transport and comparison. -/
theorem right_first_anchor_small :
    rightStartingAnchor P u v w ≪≫ BassH1References.firstIso P u (v ≫ w) =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (right_first_total P u v w)) ≪≫
        boundedFlatNormalizedPullbackCompIso
          (coefficientMap P ((laurentUnderFunctor R).map (v ≫ w)))
          (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)) := by
  rw [right_starting_anchor_h0, h0_anchor_small, BassH1References.firstIso,
    ← smallIso_trans, ← Iso.trans_assoc, eqToIso_trans]

/-- The left-middle anchor exposes only its original raw transport and comparison. -/
theorem left_middle_anchor_small :
    h0Anchor P (u ≫ v) w ≪≫ BassH1References.middleIso P (u ≫ v) w =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (left_middle_total P u v w)) ≪≫
        boundedFlatNormalizedPullbackCompIso
          (coefficientMap P ((laurentUnderFunctor R).map w) ≫ laurentProjection P c)
          (coefficientMap P (u ≫ v))) := by
  rw [h0_anchor_small, BassH1References.middleIso,
    ← smallIso_trans, ← Iso.trans_assoc, eqToIso_trans]

/-- The complete right-first reference changes by the actual Laurent comparison and associator. -/
theorem right_first_composition_anchor :
    (rightStartingAnchor P u v w ≪≫ BassH1References.firstIso P u (v ≫ w)) ≪≫
        isoWhiskerLeft (BassH0Diagram.reference P u).functor (laurentCompositionIso P v w) ≪≫
        (Functor.associator (BassH0Diagram.reference P u).functor
          (coefficientModel P ((laurentUnderFunctor R).map v)).functor
          (coefficientModel P ((laurentUnderFunctor R).map w)).functor).symm =
      postcompAnchor P u v w ≪≫ isoWhiskerRight (BassH1References.firstIso P u v)
        (coefficientModel P ((laurentUnderFunctor R).map w)).functor := by
  have hA : (Functor.associator (BassH0Diagram.reference P u).functor
      (coefficientModel P ((laurentUnderFunctor R).map v)).functor
      (coefficientModel P ((laurentUnderFunctor R).map w)).functor).symm = Iso.refl _ := rfl
  have hS : isoWhiskerLeft (BassH0Diagram.reference P u).functor
      (laurentCompositionIso P v w) ≪≫
      (Functor.associator (BassH0Diagram.reference P u).functor
        (coefficientModel P ((laurentUnderFunctor R).map v)).functor
        (coefficientModel P ((laurentUnderFunctor R).map w)).functor).symm =
      isoWhiskerLeft (BassH0Diagram.reference P u).functor
        (laurentCompositionIso P v w) := by
    rw [hA]
    exact Iso.trans_refl _
  refine (congrArg (fun e ↦ (rightStartingAnchor P u v w ≪≫
    BassH1References.firstIso P u (v ≫ w)) ≪≫ e) hS).trans ?_
  rw [right_first_anchor_small, postcomp_anchor_small,
    laurentCompositionIso, BassH1References.firstIso]
  erw [smallIso_precomp, smallIso_postcomp]
  have hraw := anchored_factorizations_strict
    (coefficientMap P ((laurentUnderFunctor R).map w))
    (coefficientMap P ((laurentUnderFunctor R).map v))
    (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)
    (coefficientMap P ((laurentUnderFunctor R).map (v ≫ w)))
    (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
    _ (laurentComposition_total P v w) (BassH1References.first_total P u v).symm
    (right_first_total P u v w) (postcomp_total P u v w)
  simpa only [smallIso_trans, Iso.trans_assoc] using congrArg smallIso hraw

/-- The complete left-middle reference changes by the coefficient comparison and associator. -/
theorem left_middle_composition_anchor :
    (h0Anchor P (u ≫ v) w ≪≫ BassH1References.middleIso P (u ≫ v) w) ≪≫
        isoWhiskerRight (coefficientCompositionIso P u v) (BassH0Diagram.reference P w).functor ≪≫
        Functor.associator (coefficientModel P u).functor (coefficientModel P v).functor
          (BassH0Diagram.reference P w).functor =
      precompAnchor P u v w ≪≫ isoWhiskerLeft (coefficientModel P u).functor
        (BassH1References.middleIso P v w) := by
  have hA : Functor.associator (coefficientModel P u).functor (coefficientModel P v).functor
      (BassH0Diagram.reference P w).functor = Iso.refl _ := rfl
  have hS : isoWhiskerRight (coefficientCompositionIso P u v)
      (BassH0Diagram.reference P w).functor ≪≫
      Functor.associator (coefficientModel P u).functor (coefficientModel P v).functor
        (BassH0Diagram.reference P w).functor =
      isoWhiskerRight (coefficientCompositionIso P u v)
        (BassH0Diagram.reference P w).functor := by
    rw [hA]
    exact Iso.trans_refl _
  refine (congrArg (fun e ↦ (h0Anchor P (u ≫ v) w ≪≫
    BassH1References.middleIso P (u ≫ v) w) ≪≫ e) hS).trans ?_
  rw [left_middle_anchor_small, precomp_anchor_small,
    coefficientCompositionIso, BassH1References.middleIso]
  erw [smallIso_postcomp, smallIso_precomp]
  have hraw := (anchored_factorizations_strict
    (coefficientMap P ((laurentUnderFunctor R).map w) ≫ laurentProjection P c)
    (coefficientMap P v) (coefficientMap P u)
    (laurentProjection P d ≫ coefficientMap P w ≫ coefficientMap P v)
    (coefficientMap P (u ≫ v)) _ (BassH1References.middle_total P v w).symm
    (coefficientMap_comp P u v) (precomp_total P u v w) (left_middle_total P u v w)).symm
  simpa only [smallIso_trans, Iso.trans_assoc] using congrArg smallIso hraw

private theorem reference_comparison_of_square {C : Type*} [Category* C]
    {F A B X Y : C} (e : F ≅ A) (f : F ≅ B) (ρ : A ≅ X) (σ : B ≅ Y)
    (κ : A ≅ B) (κ' : X ≅ Y) (ha : e ≪≫ κ = f) (hn : ρ ≪≫ κ' = κ ≪≫ σ) :
    (e ≪≫ ρ).symm ≪≫ (f ≪≫ σ) = κ' := by
  have h : f ≪≫ σ = (e ≪≫ ρ) ≪≫ κ' := by
    rw [← ha, Iso.trans_assoc, ← hn, ← Iso.trans_assoc]
  rw [h, ← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

private theorem post_reference_comparison
    {C D E T : Type*} [Category* C] [Category* D] [Category* E] [Category* T]
    {H N : C ⥤ D} {J : D ⥤ E} {K : E ⥤ T} {L : D ⥤ T} {F : C ⥤ T}
    (e : F ≅ H ⋙ L) (f : F ≅ (H ⋙ J) ⋙ K) (ρ : H ≅ N) (κ : L ≅ J ⋙ K)
    (ha : e ≪≫ isoWhiskerLeft H κ ≪≫ (Functor.associator H J K).symm = f) :
    (e ≪≫ isoWhiskerRight ρ L).symm ≪≫
        (f ≪≫ isoWhiskerRight (isoWhiskerRight ρ J) K) =
      isoWhiskerLeft N κ ≪≫ (Functor.associator N J K).symm := by
  apply reference_comparison_of_square e f _ _ _ _ ha
  have hH : (Functor.associator H J K).symm = Iso.refl _ := rfl
  have hN : (Functor.associator N J K).symm = Iso.refl _ := rfl
  have hρ : isoWhiskerRight (isoWhiskerRight ρ J) K = isoWhiskerRight ρ (J ⋙ K) := rfl
  rw [hH, hN, hρ, Iso.trans_refl, Iso.trans_refl]
  exact (isoWhiskerLeft_trans_isoWhiskerRight ρ κ).symm

private theorem pre_reference_comparison
    {C D E T : Type*} [Category* C] [Category* D] [Category* E] [Category* T]
    {H N : E ⥤ T} {J : C ⥤ D} {K : D ⥤ E} {L : C ⥤ E} {F : C ⥤ T}
    (e : F ≅ L ⋙ H) (f : F ≅ J ⋙ K ⋙ H) (ρ : H ≅ N) (κ : L ≅ J ⋙ K)
    (ha : e ≪≫ isoWhiskerRight κ H ≪≫ Functor.associator J K H = f) :
    (e ≪≫ isoWhiskerLeft L ρ).symm ≪≫
        (f ≪≫ isoWhiskerLeft J (isoWhiskerLeft K ρ)) =
      isoWhiskerRight κ N ≪≫ Functor.associator J K N := by
  apply reference_comparison_of_square e f _ _ _ _ ha
  have hH : Functor.associator J K H = Iso.refl _ := rfl
  have hN : Functor.associator J K N = Iso.refl _ := rfl
  have hρ : isoWhiskerLeft J (isoWhiskerLeft K ρ) = isoWhiskerLeft (J ⋙ K) ρ := rfl
  rw [hH, hN, hρ, Iso.trans_refl, Iso.trans_refl]
  exact isoWhiskerLeft_trans_isoWhiskerRight κ ρ

private theorem node_comparison_heq {V W : Model.{u}} {F : V ⟶ W}
    {n n' m m' : CommonReferenceNerve.Node F} (hn : n = n') (hm : m = m') :
    HEq (n.2.symm ≪≫ m.2) (n'.2.symm ≪≫ m'.2) := by
  subst n'
  subst m'
  rfl

private theorem laurent_model_eq {a b : Under R} (u : a ⟶ b) :
    BassH1Components.laurentMap P u =
      coefficientModel P ((laurentUnderFunctor R).map u) := rfl

private theorem coefficient_model_eq {a b : Under R} (u : a ⟶ b) :
    BassH1Components.coefficientMapModel P u = coefficientModel P u := rfl

/-- Each of the 31 right-first canonical arrows retains its complete original node references.
The heterogeneous equality only transports the endpoints through the actual full node lookups. -/
theorem right_first_node_comparison (i : Fin 31) :
    HEq ((ModelSimplex.reanchorNodes (rightStartingAnchor P u v w)
        (BassMWhole.nodes P u (v ≫ w)) (firstIndex i)).2.symm ≪≫
      (postcompNodes P u v w (firstIndex i)).2)
      (isoWhiskerLeft (BassH0Diagram.nodes P u i).1.functor (laurentCompositionIso P v w) ≪≫
        (Functor.associator (BassH0Diagram.nodes P u i).1.functor
          (coefficientModel P ((laurentUnderFunctor R).map v)).functor
          (coefficientModel P ((laurentUnderFunctor R).map w)).functor).symm) := by
  have hs := congrArg (fun N ↦ ModelSimplex.reanchorNodes (rightStartingAnchor P u v w)
    (fun _ : Fin 1 ↦ N) 0) (first_nodes P u (v ≫ w) i)
  have ht := reanchor_postcomp_nodes
    (coefficientModel P ((laurentUnderFunctor R).map w)) (postcompAnchor P u v w)
    (BassH1References.firstIso P u v) _ _ firstIndex (first_nodes P u v) i
  refine (node_comparison_heq hs ht).trans ?_
  apply heq_of_eq
  simpa only [ModelSimplex.reanchorNodes, BassH1References.firstNodes,
    BassH1Components.firstNodes, CommonReferenceNerve.postcompNode, laurent_model_eq,
    Iso.trans_assoc] using
    post_reference_comparison
      (rightStartingAnchor P u v w ≪≫ BassH1References.firstIso P u (v ≫ w))
      (postcompAnchor P u v w ≪≫ isoWhiskerRight (BassH1References.firstIso P u v)
        (coefficientModel P ((laurentUnderFunctor R).map w)).functor)
      (BassH0Diagram.nodes P u i).2 (laurentCompositionIso P v w)
      (right_first_composition_anchor P u v w)

/-- Each of the 31 left-middle canonical arrows retains the actual distinct endpoint nodes. -/
theorem left_middle_node_comparison (i : Fin 31) :
    HEq ((ModelSimplex.reanchorNodes (h0Anchor P (u ≫ v) w)
        (BassMWhole.nodes P (u ≫ v) w) (middleIndex i)).2.symm ≪≫
      (precompNodes P u v w (middleIndex i)).2)
      (isoWhiskerRight (coefficientCompositionIso P u v) (BassH0Diagram.nodes P w i).1.functor ≪≫
        Functor.associator (coefficientModel P u).functor (coefficientModel P v).functor
          (BassH0Diagram.nodes P w i).1.functor) := by
  have hs := congrArg (fun N ↦ ModelSimplex.reanchorNodes (h0Anchor P (u ≫ v) w)
    (fun _ : Fin 1 ↦ N) 0) (middle_nodes P (u ≫ v) w i)
  have ht := reanchor_precomp_nodes (coefficientModel P u) (precompAnchor P u v w)
    (BassH1References.middleIso P v w) _ _ middleIndex (middle_nodes P v w) i
  refine (node_comparison_heq hs ht).trans ?_
  apply heq_of_eq
  simpa only [ModelSimplex.reanchorNodes, BassH1References.middleNodes,
    BassH1Components.middleNodes, CommonReferenceNerve.precompNode, coefficient_model_eq,
    Iso.trans_assoc] using
    pre_reference_comparison
      (h0Anchor P (u ≫ v) w ≪≫ BassH1References.middleIso P (u ≫ v) w)
      (precompAnchor P u v w ≪≫ isoWhiskerLeft (coefficientModel P u).functor
        (BassH1References.middleIso P v w))
      (BassH0Diagram.nodes P w i).2 (coefficientCompositionIso P u v)
      (left_middle_composition_anchor P u v w)

/-- The right-first source functor is exposed by the actual full node lookup. -/
theorem right_first_source_functor (i : Fin 31) :
    (ModelSimplex.reanchorNodes (rightStartingAnchor P u v w)
      (BassMWhole.nodes P u (v ≫ w)) (firstIndex i)).1.functor =
      (BassH0Diagram.nodes P u i).1.functor ⋙
        (coefficientModel P ((laurentUnderFunctor R).map (v ≫ w))).functor := by
  exact congrArg (fun N ↦ N.1.functor)
    (congrArg (fun N ↦ ModelSimplex.reanchorNodes (rightStartingAnchor P u v w)
      (fun _ : Fin 1 ↦ N) 0) (first_nodes P u (v ≫ w) i))

/-- The post-first endpoint is exposed from the complete original dependent node. -/
theorem right_first_target_functor (i : Fin 31) :
    (postcompNodes P u v w (firstIndex i)).1.functor =
      ((BassH0Diagram.nodes P u i).1.functor ⋙
        (coefficientModel P ((laurentUnderFunctor R).map v)).functor) ⋙
          (coefficientModel P ((laurentUnderFunctor R).map w)).functor := by
  exact congrArg (fun N ↦ N.1.functor)
    (congrArg (fun N ↦ ModelSimplex.reanchorNodes (postcompAnchor P u v w)
      (fun _ : Fin 1 ↦ CommonReferenceNerve.postcompNode
        (coefficientModel P ((laurentUnderFunctor R).map w)) N) 0) (first_nodes P u v i))

/-- The left-middle source keeps its exact original indexed endpoint. -/
theorem left_middle_source_functor (i : Fin 31) :
    (ModelSimplex.reanchorNodes (h0Anchor P (u ≫ v) w)
      (BassMWhole.nodes P (u ≫ v) w) (middleIndex i)).1.functor =
      (coefficientModel P (u ≫ v)).functor ⋙ (BassH0Diagram.nodes P w i).1.functor := by
  exact congrArg (fun N ↦ N.1.functor)
    (congrArg (fun N ↦ ModelSimplex.reanchorNodes (h0Anchor P (u ≫ v) w)
      (fun _ : Fin 1 ↦ N) 0) (middle_nodes P (u ≫ v) w i))

/-- The pre-middle endpoint is exposed from the complete original dependent node. -/
theorem left_middle_target_functor (i : Fin 31) :
    (precompNodes P u v w (middleIndex i)).1.functor =
      (coefficientModel P u).functor ⋙ (coefficientModel P v).functor ⋙
        (BassH0Diagram.nodes P w i).1.functor := by
  exact congrArg (fun N ↦ N.1.functor)
    (congrArg (fun N ↦ ModelSimplex.reanchorNodes (precompAnchor P u v w)
      (fun _ : Fin 1 ↦ CommonReferenceNerve.precompNode (coefficientModel P u) N) 0)
        (middle_nodes P v w i))

/-- Canonical Laurent comparison between the exact original indexed endpoint functors. -/
def rightFirstComparisonIso (i : Fin 31) :
    (ModelSimplex.reanchorNodes (rightStartingAnchor P u v w)
      (BassMWhole.nodes P u (v ≫ w)) (firstIndex i)).1.functor ≅
      (postcompNodes P u v w (firstIndex i)).1.functor :=
  eqToIso (right_first_source_functor P u v w i) ≪≫
    (isoWhiskerLeft (BassH0Diagram.nodes P u i).1.functor (laurentCompositionIso P v w) ≪≫
      (Functor.associator (BassH0Diagram.nodes P u i).1.functor
        (coefficientModel P ((laurentUnderFunctor R).map v)).functor
        (coefficientModel P ((laurentUnderFunctor R).map w)).functor).symm) ≪≫
      (eqToIso (right_first_target_functor P u v w i)).symm

/-- Canonical coefficient comparison between the exact original indexed endpoint functors. -/
def leftMiddleComparisonIso (i : Fin 31) :
    (ModelSimplex.reanchorNodes (h0Anchor P (u ≫ v) w)
      (BassMWhole.nodes P (u ≫ v) w) (middleIndex i)).1.functor ≅
      (precompNodes P u v w (middleIndex i)).1.functor :=
  eqToIso (left_middle_source_functor P u v w i) ≪≫
    (isoWhiskerRight (coefficientCompositionIso P u v) (BassH0Diagram.nodes P w i).1.functor ≪≫
      Functor.associator (coefficientModel P u).functor (coefficientModel P v).functor
        (BassH0Diagram.nodes P w i).1.functor) ≪≫
      (eqToIso (left_middle_target_functor P u v w i)).symm

private theorem iso_eq_of_heq_endpoints {C : Type*} [Category* C] {A B A' B' : C}
    (f : A ≅ B) (g : A' ≅ B') (hA : A = A') (hB : B = B') (h : HEq f g) :
    f = eqToIso hA ≪≫ g ≪≫ (eqToIso hB).symm := by
  subst A'
  subst B'
  simpa only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl] using eq_of_heq h

/-- The actual 31 right-first reference comparisons equal the transported canonical isomorphisms. -/
theorem right_first_reference_comparison (i : Fin 31) :
    (ModelSimplex.reanchorNodes (rightStartingAnchor P u v w)
      (BassMWhole.nodes P u (v ≫ w)) (firstIndex i)).2.symm ≪≫
        (postcompNodes P u v w (firstIndex i)).2 = rightFirstComparisonIso P u v w i :=
  iso_eq_of_heq_endpoints _ _ _ _ (right_first_node_comparison P u v w i)

/-- The actual 31 left-middle references equal the transported coefficient isomorphisms. -/
theorem left_middle_reference_comparison (i : Fin 31) :
    (ModelSimplex.reanchorNodes (h0Anchor P (u ≫ v) w)
      (BassMWhole.nodes P (u ≫ v) w) (middleIndex i)).2.symm ≪≫
        (precompNodes P u v w (middleIndex i)).2 = leftMiddleComparisonIso P u v w i :=
  iso_eq_of_heq_endpoints _ _ _ _ (left_middle_node_comparison P u v w i)

end Quillen.PerfectComplexes.BassMWholeNerve
