/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.UnitTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BinaryNormalizationSimplex
public import Quillen.Waldhausen.SConstruction.Iterated.UnitPrismParameters
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexLiftPasting
public import Quillen.Waldhausen.SConstruction.Iterated.ScalarRouteExtraction
public import Quillen.Topology.Prespectrum.RelativeOperationEvaluation

/-!
# A common six-node simplex for the chosen postcomposition unit track

The actual geometric comparison, binary normalization and three original unit actions provide
six full reference nodes. The scalar comparison retains the whole chosen UnitTrack recipe,
including its initial associator from the original left-associated source path.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.UnitTrackPostcompSimplex
private theorem relative_source_transport_level {E F : LoopPrespectrum.{u}}
    {f g : E ⟶ F} {H H' K : Homotopy f g} (e : H = H')
    (p : H.RelHomotopy K = H'.RelHomotopy K) (J : H.RelHomotopy K) (n : ℕ) :
    ((p.mp J).level n).toContinuousMap = (J.level n).toContinuousMap := by
  subst H'
  rfl

private theorem id_mpr_heq {A B : Sort u} (p : A = B) (x : B) :
    HEq (id (p.mpr x)) x := by
  cases p
  rfl

private theorem relative_heq_level {E F : LoopPrespectrum.{u}}
    {f g : E ⟶ F} {H H' K : Homotopy f g} (e : H = H')
    (J : H.RelHomotopy K) (J' : H'.RelHomotopy K) (h : HEq J' J) (n : ℕ) :
    (J'.level n).toContinuousMap = (J.level n).toContinuousMap := by
  subst H'
  exact congrArg (fun Q ↦ (Q.level n).toContinuousMap) (eq_of_heq h)

private theorem relative_level_eq_apply {E F : LoopPrespectrum.{u}}
    {f g f' g' : E ⟶ F} {H K : Homotopy f g} {H' K' : Homotopy f' g'}
    (J : H.RelHomotopy K) (J' : H'.RelHomotopy K') (n : ℕ)
    (e : (J.level n).toContinuousMap = (J'.level n).toContinuousMap)
    (r s : unitInterval) (x : E.space n) :
    J.level n (r, (s, x)) = J'.level n (r, (s, x)) :=
  DFunLike.congr_fun e (r, (s, x))

private def originalPastingTemplate {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    {A B C D : Homotopy f g} (e : A = B)
    (J : A.RelHomotopy C) (K : B.RelHomotopy D) : C.RelHomotopy D :=
  J.symm.trans ((congrArg (fun H ↦ H.RelHomotopy D) e.symm).mp K)

private theorem originalPastingTemplate_apply {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    {A B C D : Homotopy f g} (e : A = B)
    (J : A.RelHomotopy C) (K : B.RelHomotopy D)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (originalPastingTemplate e J K).level n (r, (s, x)) =
      if hr : (r : ℝ) ≤ 1 / 2 then
        J.level n (unitInterval.symm ⟨2 * r, (unitInterval.mul_pos_mem_iff zero_lt_two).2
          ⟨r.2.1, hr⟩⟩, (s, x))
      else K.level n (⟨2 * r - 1, unitInterval.two_mul_sub_one_mem_iff.2
        ⟨(not_le.1 hr).le, r.2.2⟩⟩, (s, x)) := by
  apply Homotopy.RelHomotopy.level_symm_trans_replace
  exact relative_source_transport_level e.symm _ _ n

private theorem originalPastingTemplate_lift {V W : Model.{u}}
    (S : ModelSimplex V W 5) {f g : prespectrum V ⟶ prespectrum W}
    {A B C D : Homotopy f g} (e : A = B) (J : A.RelHomotopy C) (K : B.RelHomotopy D)
    (hJ : HomotopyLift S (triangle UnitPrismNodes.geometricFirst) J)
    (hK : HomotopyLift S (triangle UnitPrismNodes.geometricSecond) K) :
    HomotopyLift S UnitPrismParameters.geometric (originalPastingTemplate e J K) :=
  HomotopyLift.trans S (HomotopyLift.symm S hJ)
    (HomotopyLift.nativeCast S hK e.symm rfl
      (congrArg (fun H ↦ H.RelHomotopy D) e.symm))

private theorem homotopyLift_of_apply {V W : Model.{u}} (S : ModelSimplex V W 5)
    {a b : StdSimplex ℝ (Fin 6)} {p q : Path a b} (P : p.Homotopy q)
    {f g : prespectrum V ⟶ prespectrum W} {H K : Homotopy f g} (J : H.RelHomotopy K)
    (h : ∀ n r s x, prespectrumSimplexFamily S n (P (r, s), x) =
      J.level n (r, (s, x))) : HomotopyLift S P J := h

private theorem homotopyLift_apply {V W : Model.{u}} (S : ModelSimplex V W 5)
    {a b : StdSimplex ℝ (Fin 6)} {p q : Path a b} (P : p.Homotopy q)
    {f g : prespectrum V ⟶ prespectrum W} {H K : Homotopy f g} (J : H.RelHomotopy K)
    (h : HomotopyLift S P J) (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily S n (P (r, s), x) = J.level n (r, (s, x)) := h n r s x

private theorem homotopyLift_heq {V W : Model.{u}} (S : ModelSimplex V W 5)
    {a b : StdSimplex ℝ (Fin 6)} {p q : Path a b} (P : p.Homotopy q)
    {f g : prespectrum V ⟶ prespectrum W} {H H' K : Homotopy f g} (e : H = H')
    (J : H.RelHomotopy K) (J' : H'.RelHomotopy K) (hJ : HEq J' J)
    (h : HomotopyLift S P J) : HomotopyLift S P J' := by
  subst H'
  cases eq_of_heq hJ
  exact h

private theorem homotopyLift_eq {V W : Model.{u}} (S : ModelSimplex V W 5)
    {a b : StdSimplex ℝ (Fin 6)} {p q : Path a b} (P : p.Homotopy q)
    {f g : prespectrum V ⟶ prespectrum W} {H K : Homotopy f g}
    {J J' : H.RelHomotopy K} (e : J = J') (h : HomotopyLift S P J') :
    HomotopyLift S P J := by
  cases e
  exact h

section OriginalLevels
universe v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Waldhausen.Structure C) (V : Waldhausen.Structure D) {F G G' H : C ⥤ D}
  (hF : Waldhausen.IsExact W.cof W.weq V.cof V.weq F)
  (hG : Waldhausen.IsExact W.cof W.weq V.cof V.weq G)
  (hG' : Waldhausen.IsExact W.cof W.weq V.cof V.weq G')
  (hH : Waldhausen.IsExact W.cof W.weq V.cof V.weq H)

private theorem exact_triangle_source_eq (η : F ⟶ G) (θ : G ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A)) :
    originalPrespectrumTransformationHomotopy W V hF.rebase hH.rebase
      (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _)
      (Waldhausen.normalizedWeakTransformation hF hG η ≫
        Waldhausen.normalizedWeakTransformation hG hH θ)
      (fun A ↦ V.weq.comp_mem _ _
        (Waldhausen.normalizedWeakTransformation_weak hF hG η hη A)
        (Waldhausen.normalizedWeakTransformation_weak hG hH θ hθ A)) =
    exactOriginalPrespectrumHomotopy W V hF hH (η ≫ θ)
      (fun A ↦ V.weq.comp_mem _ _ (hη A) (hθ A)) := by
  have hcomp := normalizedWeakTransformation_comp W V hF hG hH η θ
  unfold exactOriginalPrespectrumHomotopy
  congr 1
  exact hcomp.symm

private theorem exact_triangle_heq (η : F ⟶ G) (θ : G ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A)) :
    HEq (exactOriginalPrespectrumCompositionHomotopy W V hF hG hH η θ hη hθ)
    (originalPrespectrumTransformationCompositionHomotopy W V hF.rebase hG.rebase hH.rebase
      (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _)
      (Quillen.rebaseFunctor_obj_base _ _ _ _)
      (Waldhausen.normalizedWeakTransformation hF hG η)
      (Waldhausen.normalizedWeakTransformation hG hH θ)
      (Waldhausen.normalizedWeakTransformation_weak hF hG η hη)
      (Waldhausen.normalizedWeakTransformation_weak hG hH θ hθ)) := by
  unfold exactOriginalPrespectrumCompositionHomotopy
  exact id_mpr_heq _ _

private theorem exact_triangle_level (η : F ⟶ G) (θ : G ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A)) (n : ℕ) :
    ((exactOriginalPrespectrumCompositionHomotopy W V hF hG hH η θ hη hθ).level n).toContinuousMap =
    ((originalPrespectrumTransformationCompositionHomotopy W V hF.rebase hG.rebase hH.rebase
      (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _)
      (Quillen.rebaseFunctor_obj_base _ _ _ _)
      (Waldhausen.normalizedWeakTransformation hF hG η)
      (Waldhausen.normalizedWeakTransformation hG hH θ)
      (Waldhausen.normalizedWeakTransformation_weak hF hG η hη)
      (Waldhausen.normalizedWeakTransformation_weak hG hH θ hθ)).level n).toContinuousMap := by
  exact relative_heq_level (exact_triangle_source_eq W V hF hG hH η θ hη hθ)
    _ _ (exact_triangle_heq W V hF hG hH η θ hη hθ) n

private theorem exact_triangle_apply (η : F ⟶ G) (θ : G ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A)) (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum W).space n) :
    (exactOriginalPrespectrumCompositionHomotopy W V hF hG hH η θ hη hθ).level n
      (r, (s, x)) =
    (originalPrespectrumTransformationCompositionHomotopy W V hF.rebase hG.rebase hH.rebase
      (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _)
      (Quillen.rebaseFunctor_obj_base _ _ _ _)
      (Waldhausen.normalizedWeakTransformation hF hG η)
      (Waldhausen.normalizedWeakTransformation hG hH θ)
      (Waldhausen.normalizedWeakTransformation_weak hF hG η hη)
      (Waldhausen.normalizedWeakTransformation_weak hG hH θ hθ)).level n (r, (s, x)) :=
  relative_level_eq_apply _ _ n
    (exact_triangle_level W V hF hG hH η θ hη hθ n) r s x

private theorem exact_composite_track_eq
    (η : F ⟶ G) (θ : G ⟶ H) (η' : F ⟶ G') (θ' : G' ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (hη' : ∀ A, V.weq (η'.app A)) (hθ' : ∀ A, V.weq (θ'.app A))
    (he : η ≫ θ = η' ≫ θ') :
    exactOriginalPrespectrumHomotopy W V hF hH (η ≫ θ)
      (fun A ↦ V.weq.comp_mem _ _ (hη A) (hθ A)) =
      exactOriginalPrespectrumHomotopy W V hF hH (η' ≫ θ')
        (fun A ↦ V.weq.comp_mem _ _ (hη' A) (hθ' A)) := by
  congr 1

private theorem exact_pasting_eq_template
    (η : F ⟶ G) (θ : G ⟶ H) (η' : F ⟶ G') (θ' : G' ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (hη' : ∀ A, V.weq (η'.app A)) (hθ' : ∀ A, V.weq (θ'.app A))
    (he : η ≫ θ = η' ≫ θ') :
    exactOriginalPrespectrumPastingHomotopy W V hF hG hG' hH
      η θ η' θ' hη hθ hη' hθ' he =
    originalPastingTemplate (exact_composite_track_eq W V hF hH
      η θ η' θ' hη hθ hη' hθ' he)
      (exactOriginalPrespectrumCompositionHomotopy W V hF hG hH η θ hη hθ)
      (exactOriginalPrespectrumCompositionHomotopy W V hF hG' hH η' θ' hη' hθ') := rfl

private theorem exact_pasting_apply
    (η : F ⟶ G) (θ : G ⟶ H) (η' : F ⟶ G') (θ' : G' ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (hη' : ∀ A, V.weq (η'.app A)) (hθ' : ∀ A, V.weq (θ'.app A))
    (he : η ≫ θ = η' ≫ θ') (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum W).space n) :
    (exactOriginalPrespectrumPastingHomotopy W V hF hG hG' hH
      η θ η' θ' hη hθ hη' hθ' he).level n (r, (s, x)) =
      if hr : (r : ℝ) ≤ 1 / 2 then
        (exactOriginalPrespectrumCompositionHomotopy W V hF hG hH η θ hη hθ).level n
          (unitInterval.symm ⟨2 * r, (unitInterval.mul_pos_mem_iff zero_lt_two).2
            ⟨r.2.1, hr⟩⟩, (s, x))
      else
        (exactOriginalPrespectrumCompositionHomotopy W V hF hG' hH η' θ' hη' hθ').level n
          (⟨2 * r - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 hr).le, r.2.2⟩⟩, (s, x)) := by
  exact (congrArg (fun J ↦ J.level n (r, (s, x)))
    (exact_pasting_eq_template W V hF hG hG' hH η θ η' θ' hη hθ hη' hθ' he)).trans
      (originalPastingTemplate_apply _ _ _ n r s x)

private theorem original_triangle_lift
    (h0F : F.obj W.zero = V.zero) (h0G : G.obj W.zero = V.zero)
    (h0H : H.obj W.zero = V.zero) (η : F ⟶ G) (θ : G ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (S : ModelSimplex (modelOf W) (modelOf V) 5) (α : ⦋2⦌ ⟶ ⦋5⦌)
    (hface : S.face α = ModelSimplex.triangle
      (F := modelMap W V hF h0F) (G := modelMap W V hG h0G)
      (H := modelMap W V hH h0H)
      (whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
      (whiskerLeft AsSmall.down (whiskerRight θ AsSmall.up))
      (fun A ↦ hη (AsSmall.down.obj A)) (fun A ↦ hθ (AsSmall.down.obj A)))
    (n : ℕ) (r s : unitInterval) (x : (originalPrespectrum W).space n) :
    prespectrumSimplexFamily S n (triangle α (r, s), x) =
      (originalPrespectrumTransformationCompositionHomotopy W V hF hG hH
        h0F h0G h0H η θ hη hθ).level n (r, (s, x)) :=
  triangle_lift S α _ _ _ _ hface n r s x

private theorem normalized_triangle_lift (η : F ⟶ G) (θ : G ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (S : ModelSimplex (modelOf W) (modelOf V) 5) (α : ⦋2⦌ ⟶ ⦋5⦌)
    (hface : S.face α = ModelSimplex.triangle
      (F := modelMap W V hF.rebase (Quillen.rebaseFunctor_obj_base _ _ _ _))
      (G := modelMap W V hG.rebase (Quillen.rebaseFunctor_obj_base _ _ _ _))
      (H := modelMap W V hH.rebase (Quillen.rebaseFunctor_obj_base _ _ _ _))
      (whiskerLeft AsSmall.down
        (whiskerRight (Waldhausen.normalizedWeakTransformation hF hG η) AsSmall.up))
      (whiskerLeft AsSmall.down
        (whiskerRight (Waldhausen.normalizedWeakTransformation hG hH θ) AsSmall.up))
      (fun A ↦ Waldhausen.normalizedWeakTransformation_weak hF hG η hη (AsSmall.down.obj A))
      (fun A ↦ Waldhausen.normalizedWeakTransformation_weak hG hH θ hθ (AsSmall.down.obj A)))
    (n : ℕ) (r s : unitInterval) (x : (originalPrespectrum W).space n) :
    prespectrumSimplexFamily S n (triangle α (r, s), x) =
      (originalPrespectrumTransformationCompositionHomotopy W V hF.rebase hG.rebase hH.rebase
        (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _)
        (Quillen.rebaseFunctor_obj_base _ _ _ _)
        (Waldhausen.normalizedWeakTransformation hF hG η)
        (Waldhausen.normalizedWeakTransformation hG hH θ)
        (Waldhausen.normalizedWeakTransformation_weak hF hG η hη)
        (Waldhausen.normalizedWeakTransformation_weak hG hH θ hθ)).level n
        (r, (s, x)) :=
  original_triangle_lift W V hF.rebase hG.rebase hH.rebase _ _ _
    (Waldhausen.normalizedWeakTransformation hF hG η)
    (Waldhausen.normalizedWeakTransformation hG hH θ)
    (Waldhausen.normalizedWeakTransformation_weak hF hG η hη)
    (Waldhausen.normalizedWeakTransformation_weak hG hH θ hθ) S α hface n r s x

private theorem exact_triangle_apply_lift (η : F ⟶ G) (θ : G ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (S : ModelSimplex (modelOf W) (modelOf V) 5) (α : ⦋2⦌ ⟶ ⦋5⦌)
    (hface : S.face α = ModelSimplex.triangle
      (F := modelMap W V hF.rebase (Quillen.rebaseFunctor_obj_base _ _ _ _))
      (G := modelMap W V hG.rebase (Quillen.rebaseFunctor_obj_base _ _ _ _))
      (H := modelMap W V hH.rebase (Quillen.rebaseFunctor_obj_base _ _ _ _))
      (whiskerLeft AsSmall.down
        (whiskerRight (Waldhausen.normalizedWeakTransformation hF hG η) AsSmall.up))
      (whiskerLeft AsSmall.down
        (whiskerRight (Waldhausen.normalizedWeakTransformation hG hH θ) AsSmall.up))
      (fun A ↦ Waldhausen.normalizedWeakTransformation_weak hF hG η hη (AsSmall.down.obj A))
      (fun A ↦ Waldhausen.normalizedWeakTransformation_weak hG hH θ hθ (AsSmall.down.obj A)))
    (n : ℕ) (r s : unitInterval) (x : (originalPrespectrum W).space n) :
    prespectrumSimplexFamily S n (triangle α (r, s), x) =
      (exactOriginalPrespectrumCompositionHomotopy W V hF hG hH η θ hη hθ).level n
        (r, (s, x)) := by
  exact (normalized_triangle_lift W V hF hG hH η θ hη hθ S α hface n r s x).trans
    (exact_triangle_apply W V hF hG hH η θ hη hθ n r s x).symm


private theorem normalized_triangle_lift_whole (η : F ⟶ G) (θ : G ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (S : ModelSimplex (modelOf W) (modelOf V) 5) (α : ⦋2⦌ ⟶ ⦋5⦌)
    (hface : S.face α = ModelSimplex.triangle
      (F := modelMap W V hF.rebase (Quillen.rebaseFunctor_obj_base _ _ _ _))
      (G := modelMap W V hG.rebase (Quillen.rebaseFunctor_obj_base _ _ _ _))
      (H := modelMap W V hH.rebase (Quillen.rebaseFunctor_obj_base _ _ _ _))
      (whiskerLeft AsSmall.down
        (whiskerRight (Waldhausen.normalizedWeakTransformation hF hG η) AsSmall.up))
      (whiskerLeft AsSmall.down
        (whiskerRight (Waldhausen.normalizedWeakTransformation hG hH θ) AsSmall.up))
      (fun A ↦ Waldhausen.normalizedWeakTransformation_weak hF hG η hη (AsSmall.down.obj A))
      (fun A ↦ Waldhausen.normalizedWeakTransformation_weak hG hH θ hθ (AsSmall.down.obj A)))
    : HomotopyLift S (triangle α)
      (originalPrespectrumTransformationCompositionHomotopy W V hF.rebase hG.rebase hH.rebase
        (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _)
        (Quillen.rebaseFunctor_obj_base _ _ _ _)
        (Waldhausen.normalizedWeakTransformation hF hG η)
        (Waldhausen.normalizedWeakTransformation hG hH θ)
        (Waldhausen.normalizedWeakTransformation_weak hF hG η hη)
        (Waldhausen.normalizedWeakTransformation_weak hG hH θ hθ)) :=
  homotopyLift_of_apply S (triangle α) _
    (normalized_triangle_lift W V hF hG hH η θ hη hθ S α hface)


private theorem exact_triangle_lift (η : F ⟶ G) (θ : G ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (S : ModelSimplex (modelOf W) (modelOf V) 5) (α : ⦋2⦌ ⟶ ⦋5⦌)
    (hface : S.face α = ModelSimplex.triangle
      (F := modelMap W V hF.rebase (Quillen.rebaseFunctor_obj_base _ _ _ _))
      (G := modelMap W V hG.rebase (Quillen.rebaseFunctor_obj_base _ _ _ _))
      (H := modelMap W V hH.rebase (Quillen.rebaseFunctor_obj_base _ _ _ _))
      (whiskerLeft AsSmall.down
        (whiskerRight (Waldhausen.normalizedWeakTransformation hF hG η) AsSmall.up))
      (whiskerLeft AsSmall.down
        (whiskerRight (Waldhausen.normalizedWeakTransformation hG hH θ) AsSmall.up))
      (fun A ↦ Waldhausen.normalizedWeakTransformation_weak hF hG η hη (AsSmall.down.obj A))
      (fun A ↦ Waldhausen.normalizedWeakTransformation_weak hG hH θ hθ (AsSmall.down.obj A)))
    : HomotopyLift S (triangle α)
      (exactOriginalPrespectrumCompositionHomotopy W V hF hG hH η θ hη hθ) :=
  homotopyLift_heq S (triangle α) (exact_triangle_source_eq W V hF hG hH η θ hη hθ)
    _ _ (exact_triangle_heq W V hF hG hH η θ hη hθ)
    (normalized_triangle_lift_whole W V hF hG hH η θ hη hθ S α hface)


private theorem normalization_original_lift
    (h0F : F.obj W.zero = V.zero) (h0G : G.obj W.zero = V.zero)
    (h0G' : G'.obj W.zero = V.zero) (h0H : H.obj W.zero = V.zero)
    (η : F ⟶ G) (θ : G ⟶ H) (η' : F ⟶ G') (θ' : G' ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (hη' : ∀ A, V.weq (η'.app A)) (hθ' : ∀ A, V.weq (θ'.app A))
    (he : η ≫ θ = η' ≫ θ') (S : ModelSimplex (modelOf W) (modelOf V) 5)
    (hfirst : S.face UnitPrismNodes.normalizationFirst = ModelSimplex.triangle
      (F := modelMap W V hF h0F) (G := modelMap W V hG h0G)
      (H := modelMap W V hH h0H)
      (whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
      (whiskerLeft AsSmall.down (whiskerRight θ AsSmall.up))
      (fun A ↦ hη (AsSmall.down.obj A)) (fun A ↦ hθ (AsSmall.down.obj A)))
    (hsecond : S.face UnitPrismNodes.normalizationSecond = ModelSimplex.triangle
      (F := modelMap W V hF h0F) (G := modelMap W V hG' h0G')
      (H := modelMap W V hH h0H)
      (whiskerLeft AsSmall.down (whiskerRight η' AsSmall.up))
      (whiskerLeft AsSmall.down (whiskerRight θ' AsSmall.up))
      (fun A ↦ hη' (AsSmall.down.obj A)) (fun A ↦ hθ' (AsSmall.down.obj A))) :
    HomotopyLift S UnitPrismParameters.normalization
      (originalPrespectrumPastingHomotopy W V hF hG hG' hH h0F h0G h0G' h0H
        η θ η' θ' hη hθ hη' hθ' he) := by
  intro n r s x
  have h := originalPrespectrumPastingHomotopy_whole_level W V hF hG hG' hH
    h0F h0G h0G' h0H η θ η' θ' hη hθ hη' hθ' he n r s x
  refine Eq.trans ?_ h.symm
  rw [UnitPrismParameters.normalization, Path.Homotopy.trans_apply]
  split
  · exact original_triangle_lift W V hF hG hH h0F h0G h0H η θ hη hθ S
      UnitPrismNodes.normalizationFirst hfirst n _ s x
  · exact original_triangle_lift W V hF hG' hH h0F h0G' h0H η' θ' hη' hθ' S
      UnitPrismNodes.normalizationSecond hsecond n _ s x

private theorem exact_pasting_lift
    (η : F ⟶ G) (θ : G ⟶ H) (η' : F ⟶ G') (θ' : G' ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (hη' : ∀ A, V.weq (η'.app A)) (hθ' : ∀ A, V.weq (θ'.app A))
    (he : η ≫ θ = η' ≫ θ') (S : ModelSimplex (modelOf W) (modelOf V) 5)
    (hfirst : HomotopyLift S (triangle UnitPrismNodes.geometricFirst)
      (exactOriginalPrespectrumCompositionHomotopy W V hF hG hH η θ hη hθ))
    (hsecond : HomotopyLift S (triangle UnitPrismNodes.geometricSecond)
      (exactOriginalPrespectrumCompositionHomotopy W V hF hG' hH η' θ' hη' hθ')) :
    HomotopyLift S UnitPrismParameters.geometric
      (exactOriginalPrespectrumPastingHomotopy W V hF hG hG' hH
        η θ η' θ' hη hθ hη' hθ' he) :=
  homotopyLift_eq S UnitPrismParameters.geometric
    (exact_pasting_eq_template W V hF hG hG' hH η θ η' θ' hη hθ hη' hθ' he)
    (originalPastingTemplate_lift S
      (exact_composite_track_eq W V hF hH η θ η' θ' hη hθ hη' hθ' he) _ _ hfirst hsecond)

end OriginalLevels

section NormalizationLevel
universe v
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {W : Waldhausen.Structure C} {V : Waldhausen.Structure D} {U : Waldhausen.Structure E}

private theorem normalization_track_level {F F' : C ⥤ D} {G : D ⥤ E}
    (hF : Waldhausen.IsExact W.cof W.weq V.cof V.weq F)
    (hF' : Waldhausen.IsExact W.cof W.weq V.cof V.weq F')
    (hG : Waldhausen.IsExact V.cof V.weq U.cof U.weq G) (η : F ⟶ F')
    (hη : ∀ A, V.weq (η.app A)) (n : ℕ) :
    ((exactNormalizationLeftTrackPasting hF hF' hG η hη).level n).toContinuousMap =
      ((exactNormalizationLeftPasting hF hF' hG η hη).level n).toContinuousMap := rfl

private theorem normalization_track_lift {F F' : C ⥤ D} {G : D ⥤ E}
    (hF : Waldhausen.IsExact W.cof W.weq V.cof V.weq F)
    (hF' : Waldhausen.IsExact W.cof W.weq V.cof V.weq F')
    (hG : Waldhausen.IsExact V.cof V.weq U.cof U.weq G) (η : F ⟶ F')
    (hη : ∀ A, V.weq (η.app A)) (S : ModelSimplex (modelOf W) (modelOf U) 5)
    (h : HomotopyLift S UnitPrismParameters.normalization
      (exactNormalizationLeftPasting hF hF' hG η hη)) :
    HomotopyLift S UnitPrismParameters.normalization
      (exactNormalizationLeftTrackPasting hF hF' hG η hη) := by
  intro n r s x
  exact (h n r s x).trans
    (relative_level_eq_apply _ _ n (normalization_track_level hF hF' hG η hη n) r s x).symm

end NormalizationLevel



variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (r : (Γ(Y, ⊤))ˣ)

/-- The actual source unit retains its original chosen-zero conjugation. -/
def sourceUnitIso : boundedFlatNormalizedPullback (f ≫ g) ≅
    boundedFlatNormalizedPullback (f ≫ g) :=
  (boundedFlatPullbackNormalizationIso (f ≫ g)).symm ≪≫
    boundedFlatPerfectPullbackUnitIso (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r) ≪≫
      boundedFlatPullbackNormalizationIso (f ≫ g)

/-- The actual intermediate unit is normalized only after its original postwhiskering. -/
def middleUnitIso : BinaryNormalizationSimplex.intermediate f g ≅
    BinaryNormalizationSimplex.intermediate f g :=
  (Quillen.rebaseFunctorIso _ _ _ _).symm ≪≫
    isoWhiskerRight (boundedFlatPerfectPullbackUnitIso g r) (boundedFlatPerfectPullback f) ≪≫
      Quillen.rebaseFunctorIso _ _ _ _

/-- The final unit postwhiskers the already normalized original source unit. -/
def finalUnitIso :
    boundedFlatNormalizedPullback g ⋙ boundedFlatNormalizedPullback f ≅
      boundedFlatNormalizedPullback g ⋙ boundedFlatNormalizedPullback f :=
  isoWhiskerRight
    ((boundedFlatPullbackNormalizationIso g).symm ≪≫ boundedFlatPerfectPullbackUnitIso g r ≪≫
      boundedFlatPullbackNormalizationIso g) (boundedFlatNormalizedPullback f)

/-- This is precisely the original normalized source transformation. -/
theorem sourceUnitIso_hom : (sourceUnitIso f g r).hom =
    Waldhausen.normalizedWeakTransformation (boundedFlatPerfectPullback_exact (f ≫ g))
      (boundedFlatPerfectPullback_exact (f ≫ g))
      (boundedFlatPerfectPullbackUnitIso (f ≫ g)
        (Units.map f.appTop.hom.toMonoidHom r)).hom := rfl

/-- This is precisely the original normalized middle transformation. -/
theorem middleUnitIso_hom : (middleUnitIso f g r).hom =
    Waldhausen.normalizedWeakTransformation
      ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
      ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
      (whiskerRight (boundedFlatPerfectPullbackUnitIso g r).hom
        (boundedFlatPerfectPullback f)) := rfl

/-- This is precisely the original final whiskered normalized transformation. -/
theorem finalUnitIso_hom : (finalUnitIso f g r).hom =
    whiskerRight (Waldhausen.normalizedWeakTransformation (boundedFlatPerfectPullback_exact g)
      (boundedFlatPerfectPullback_exact g) (boundedFlatPerfectPullbackUnitIso g r).hom)
        (boundedFlatNormalizedPullback f) := rfl

/-- The original geometric intertwining survives the exact chosen-zero normalization. -/
theorem geometric_unit :
    (BinaryNormalizationSimplex.geometricIso f g).hom ≫ (middleUnitIso f g r).hom =
      (sourceUnitIso f g r).hom ≫ (BinaryNormalizationSimplex.geometricIso f g).hom := by
  rw [BinaryNormalizationSimplex.geometricIso_hom, middleUnitIso_hom, sourceUnitIso_hom]
  rw [← normalizedWeakTransformation_comp, ← normalizedWeakTransformation_comp]
  exact congrArg (Waldhausen.normalizedWeakTransformation
    (boundedFlatPerfectPullback_exact (f ≫ g))
    ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f)))
      (boundedFlatPerfectPullbackUnitIso_comp f g r)

/-- The original left normalization naturality square is the second unit equation. -/
theorem normalization_unit :
    (middleUnitIso f g r).hom ≫ (BinaryNormalizationSimplex.normalizationIso f g).hom =
      (BinaryNormalizationSimplex.normalizationIso f g).hom ≫ (finalUnitIso f g r).hom := by
  rw [middleUnitIso_hom, finalUnitIso_hom]
  exact exactNormalizationCompIso_natural_left (boundedFlatPerfectPullback_exact g)
    (boundedFlatPerfectPullback_exact g) (boundedFlatPerfectPullback_exact f)
    (boundedFlatPerfectPullbackUnitIso g r).hom

/-- The actual source unit in the unchanged small-model coordinates. -/
def sourceUnit : (BinaryNormalizationSimplex.sourceMap f g).functor ≅
    (BinaryNormalizationSimplex.sourceMap f g).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight (sourceUnitIso f g r) AsSmall.up)

/-- The actual middle unit in the unchanged small-model coordinates. -/
def middleUnit : (BinaryNormalizationSimplex.intermediateMap f g).functor ≅
    (BinaryNormalizationSimplex.intermediateMap f g).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight (middleUnitIso f g r) AsSmall.up)

/-- The actual final unit in the unchanged small-model coordinates. -/
def finalUnit : (BinaryNormalizationSimplex.targetMap f g).functor ≅
    (BinaryNormalizationSimplex.targetMap f g).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight (finalUnitIso f g r) AsSmall.up)

/-- Full small-model geometric components satisfy the original commuting equation. -/
theorem small_geometric_unit :
    (BinaryNormalizationSimplex.first f g).hom ≫ (middleUnit f g r).hom =
      (sourceUnit f g r).hom ≫ (BinaryNormalizationSimplex.first f g).hom := by
  have h := congrArg (fun η ↦ whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
    (geometric_unit f g r)
  simpa only [BinaryNormalizationSimplex.first, middleUnit, sourceUnit, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_comp, whiskerRight_comp] using h

/-- Full small-model normalization components satisfy the original commuting equation. -/
theorem small_normalization_unit :
    (middleUnit f g r).hom ≫ (BinaryNormalizationSimplex.second f g).hom =
      (BinaryNormalizationSimplex.second f g).hom ≫ (finalUnit f g r).hom := by
  have h := congrArg (fun η ↦ whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
    (normalization_unit f g r)
  simpa only [BinaryNormalizationSimplex.second, middleUnit, finalUnit, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_comp, whiskerRight_comp] using h

/-- All six actual dependent nodes keep the three unit-shifted reference isomorphisms. -/
def nodes := UnitPrismNodes.nodes
  (BinaryNormalizationSimplex.sourceMap f g) (BinaryNormalizationSimplex.intermediateMap f g)
  (BinaryNormalizationSimplex.targetMap f g) (BinaryNormalizationSimplex.first f g)
  (BinaryNormalizationSimplex.second f g) (sourceUnit f g r) (middleUnit f g r)
  (finalUnit f g r)

/-- The actual common simplex has no supplied higher-comparison input. -/
def simplex := UnitPrismNodes.simplex
  (BinaryNormalizationSimplex.sourceMap f g) (BinaryNormalizationSimplex.intermediateMap f g)
  (BinaryNormalizationSimplex.targetMap f g) (BinaryNormalizationSimplex.first f g)
  (BinaryNormalizationSimplex.second f g) (sourceUnit f g r) (middleUnit f g r)
  (finalUnit f g r)

/-- The unchanged geometric component G of the original postcomposition UnitTrack. -/
def geometricTrack := exactOriginalPrespectrumIsoHomotopy
  (boundedFlatPerfectWaldhausen Z) (boundedFlatPerfectWaldhausen X)
  (boundedFlatPerfectPullback_exact (f ≫ g))
  ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
  (boundedFlatPerfectPullbackCompIso f g)

/-- The unchanged binary normalization component N of the original UnitTrack. -/
def normalizationTrack := exactOriginalPrespectrumMapCompHomotopy
  (boundedFlatPerfectWaldhausen Z) (boundedFlatPerfectWaldhausen Y)
  (boundedFlatPerfectWaldhausen X) (boundedFlatPerfectPullback_exact g)
  (boundedFlatPerfectPullback_exact f)

/-- The unchanged source unit component A. -/
def sourceUnitTrack := boundedFlatPerfectUnitHomotopy (f ≫ g)
  (Units.map f.appTop.hom.toMonoidHom r)

/-- The unchanged normalized middle unit component B. -/
def middleUnitTrack := exactOriginalPrespectrumIsoHomotopy
  (boundedFlatPerfectWaldhausen Z) (boundedFlatPerfectWaldhausen X)
  ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
  ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
  (isoWhiskerRight (boundedFlatPerfectPullbackUnitIso g r) (boundedFlatPerfectPullback f))

/-- The unchanged actual postwhiskered final unit component D. -/
def finalUnitTrack := (boundedFlatPerfectUnitHomotopy g r).postcomp
  (boundedFlatPerfectPrespectrumMap f)

/-- The exact original geometric pasting JG, with its original equality certificate. -/
def geometricPasting := exactOriginalPrespectrumPastingHomotopy
  (boundedFlatPerfectWaldhausen Z) (boundedFlatPerfectWaldhausen X)
  (boundedFlatPerfectPullback_exact (f ≫ g))
  ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
  (boundedFlatPerfectPullback_exact (f ≫ g))
  ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
  (boundedFlatPerfectPullbackCompIso f g).hom
  (isoWhiskerRight (boundedFlatPerfectPullbackUnitIso g r) (boundedFlatPerfectPullback f)).hom
  (boundedFlatPerfectPullbackUnitIso (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)).hom
  (boundedFlatPerfectPullbackCompIso f g).hom
  (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
  (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
  (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
  (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
  (boundedFlatPerfectPullbackUnitIso_comp f g r)

/-- The exact original normalization pasting JN, including its full native level transport. -/
def normalizationPasting := exactNormalizationLeftTrackPasting
  (boundedFlatPerfectPullback_exact g) (boundedFlatPerfectPullback_exact g)
  (boundedFlatPerfectPullback_exact f) (boundedFlatPerfectPullbackUnitIso g r).hom
  (fun _ ↦ (boundedFlatPerfectWaldhausen Y).weq_iso _ inferInstance)

private theorem geometric_first_normalized_face :
    (simplex f g r).face UnitPrismNodes.geometricFirst =
      ModelSimplex.triangle
        (F := BinaryNormalizationSimplex.sourceMap f g)
        (G := BinaryNormalizationSimplex.intermediateMap f g)
        (H := BinaryNormalizationSimplex.intermediateMap f g)
        (whiskerLeft AsSmall.down (whiskerRight
          (Waldhausen.normalizedWeakTransformation
            (boundedFlatPerfectPullback_exact (f ≫ g))
            ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
            (boundedFlatPerfectPullbackCompIso f g).hom) AsSmall.up))
        (whiskerLeft AsSmall.down (whiskerRight
          (Waldhausen.normalizedWeakTransformation
            ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
            ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
            (isoWhiskerRight (boundedFlatPerfectPullbackUnitIso g r)
              (boundedFlatPerfectPullback f)).hom) AsSmall.up))
        (fun A ↦ Waldhausen.normalizedWeakTransformation_weak
          (boundedFlatPerfectPullback_exact (f ≫ g))
          ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
          (boundedFlatPerfectPullbackCompIso f g).hom
          (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
          (AsSmall.down.obj A))
        (fun A ↦ Waldhausen.normalizedWeakTransformation_weak
          ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
          ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
          (isoWhiskerRight (boundedFlatPerfectPullbackUnitIso g r)
            (boundedFlatPerfectPullback f)).hom
          (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
          (AsSmall.down.obj A)) := by
  simpa only [simplex, BinaryNormalizationSimplex.first, middleUnit, middleUnitIso_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, BinaryNormalizationSimplex.geometricIso_hom] using
    (UnitPrismNodes.geometric_first
    (BinaryNormalizationSimplex.sourceMap f g) (BinaryNormalizationSimplex.intermediateMap f g)
    (BinaryNormalizationSimplex.targetMap f g) (BinaryNormalizationSimplex.first f g)
    (BinaryNormalizationSimplex.second f g) (sourceUnit f g r) (middleUnit f g r)
    (finalUnit f g r))

private theorem geometric_second_normalized_face :
    (simplex f g r).face UnitPrismNodes.geometricSecond =
      ModelSimplex.triangle
        (F := BinaryNormalizationSimplex.sourceMap f g)
        (G := BinaryNormalizationSimplex.sourceMap f g)
        (H := BinaryNormalizationSimplex.intermediateMap f g)
        (whiskerLeft AsSmall.down (whiskerRight
          (Waldhausen.normalizedWeakTransformation
            (boundedFlatPerfectPullback_exact (f ≫ g))
            (boundedFlatPerfectPullback_exact (f ≫ g))
            (boundedFlatPerfectPullbackUnitIso (f ≫ g)
              (Units.map f.appTop.hom.toMonoidHom r)).hom) AsSmall.up))
        (whiskerLeft AsSmall.down (whiskerRight
          (Waldhausen.normalizedWeakTransformation
            (boundedFlatPerfectPullback_exact (f ≫ g))
            ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
            (boundedFlatPerfectPullbackCompIso f g).hom) AsSmall.up))
        (fun A ↦ Waldhausen.normalizedWeakTransformation_weak
          (boundedFlatPerfectPullback_exact (f ≫ g))
          (boundedFlatPerfectPullback_exact (f ≫ g))
          (boundedFlatPerfectPullbackUnitIso (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)).hom
          (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
          (AsSmall.down.obj A))
        (fun A ↦ Waldhausen.normalizedWeakTransformation_weak
          (boundedFlatPerfectPullback_exact (f ≫ g))
          ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
          (boundedFlatPerfectPullbackCompIso f g).hom
          (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
          (AsSmall.down.obj A)) := by
  simpa only [simplex, BinaryNormalizationSimplex.first, sourceUnit, sourceUnitIso_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, BinaryNormalizationSimplex.geometricIso_hom] using
    (UnitPrismNodes.geometric_second
    (BinaryNormalizationSimplex.sourceMap f g) (BinaryNormalizationSimplex.intermediateMap f g)
    (BinaryNormalizationSimplex.targetMap f g) (BinaryNormalizationSimplex.first f g)
    (BinaryNormalizationSimplex.second f g) (sourceUnit f g r) (middleUnit f g r)
    (finalUnit f g r) (small_geometric_unit f g r))

/-- The original geometric first triangle has its whole normalized small-model lift. -/
theorem geometric_first_lift :
    HomotopyLift (simplex f g r) (triangle UnitPrismNodes.geometricFirst)
    (exactOriginalPrespectrumCompositionHomotopy
      (boundedFlatPerfectWaldhausen Z) (boundedFlatPerfectWaldhausen X)
      (boundedFlatPerfectPullback_exact (f ≫ g))
      ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
      ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
      (boundedFlatPerfectPullbackCompIso f g).hom
      (isoWhiskerRight (boundedFlatPerfectPullbackUnitIso g r) (boundedFlatPerfectPullback f)).hom
      (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
      (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)) := by
  exact exact_triangle_lift
    (boundedFlatPerfectWaldhausen Z) (boundedFlatPerfectWaldhausen X)
    (boundedFlatPerfectPullback_exact (f ≫ g))
    ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
    ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
    (boundedFlatPerfectPullbackCompIso f g).hom
    (isoWhiskerRight (boundedFlatPerfectPullbackUnitIso g r) (boundedFlatPerfectPullback f)).hom
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (simplex f g r) UnitPrismNodes.geometricFirst
    (geometric_first_normalized_face f g r)

/-- The original geometric second triangle keeps the actual source-unit normalization. -/
theorem geometric_second_lift :
    HomotopyLift (simplex f g r) (triangle UnitPrismNodes.geometricSecond)
    (exactOriginalPrespectrumCompositionHomotopy
      (boundedFlatPerfectWaldhausen Z) (boundedFlatPerfectWaldhausen X)
      (boundedFlatPerfectPullback_exact (f ≫ g))
      (boundedFlatPerfectPullback_exact (f ≫ g))
      ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
      (boundedFlatPerfectPullbackUnitIso (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)).hom
      (boundedFlatPerfectPullbackCompIso f g).hom
      (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
      (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)) := by
  exact exact_triangle_lift
    (boundedFlatPerfectWaldhausen Z) (boundedFlatPerfectWaldhausen X)
    (boundedFlatPerfectPullback_exact (f ≫ g))
    (boundedFlatPerfectPullback_exact (f ≫ g))
    ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
    (boundedFlatPerfectPullbackUnitIso (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)).hom
    (boundedFlatPerfectPullbackCompIso f g).hom
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (simplex f g r) UnitPrismNodes.geometricSecond
    (geometric_second_normalized_face f g r)

/-- Both geometric halves recover the original equality-transported pasting at every point. -/
theorem geometricPasting_lift :
    HomotopyLift (simplex f g r) UnitPrismParameters.geometric (geometricPasting f g r) :=
  exact_pasting_lift
    (boundedFlatPerfectWaldhausen Z) (boundedFlatPerfectWaldhausen X)
    (boundedFlatPerfectPullback_exact (f ≫ g))
    ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
    (boundedFlatPerfectPullback_exact (f ≫ g))
    ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
    (boundedFlatPerfectPullbackCompIso f g).hom
    (isoWhiskerRight (boundedFlatPerfectPullbackUnitIso g r) (boundedFlatPerfectPullback f)).hom
    (boundedFlatPerfectPullbackUnitIso (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)).hom
    (boundedFlatPerfectPullbackCompIso f g).hom
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (boundedFlatPerfectPullbackUnitIso_comp f g r) (simplex f g r)
    (geometric_first_lift f g r) (geometric_second_lift f g r)

private theorem normalizationPasting_original_lift :
    HomotopyLift (simplex f g r) UnitPrismParameters.normalization
      (exactNormalizationLeftPasting (boundedFlatPerfectPullback_exact g)
        (boundedFlatPerfectPullback_exact g) (boundedFlatPerfectPullback_exact f)
        (boundedFlatPerfectPullbackUnitIso g r).hom
        (fun _ ↦ (boundedFlatPerfectWaldhausen Y).weq_iso _ inferInstance)) := by
  apply normalization_original_lift
  · exact UnitPrismNodes.normalization_first _ _ _ _ _ _ _ _
      (small_normalization_unit f g r)
  · exact UnitPrismNodes.normalization_second _ _ _ _ _ _ _ _

/-- Both individually ordered normalization triangles recover the original entire JN.
The original ofLevels endpoint transport changes neither of its independent coordinates. -/
theorem normalizationPasting_lift :
    HomotopyLift (simplex f g r) UnitPrismParameters.normalization
      (normalizationPasting f g r) :=
  normalization_track_lift (boundedFlatPerfectPullback_exact g)
    (boundedFlatPerfectPullback_exact g) (boundedFlatPerfectPullback_exact f)
    (boundedFlatPerfectPullbackUnitIso g r).hom
    (fun _ ↦ (boundedFlatPerfectWaldhausen Y).weq_iso _ inferInstance)
    (simplex f g r) (normalizationPasting_original_lift f g r)

/-- The chosen postcomposition UnitTrack itself has the exact five-piece common-simplex lift.
All original associators, both original pastings and every relative time are retained. -/
theorem native_lift :
    HomotopyLift (simplex f g r) UnitPrismParameters.parameter
      (boundedFlatPerfectUnitTrackPostcomp f g r) :=
  UnitPrismParameters.parameter_lift (simplex f g r)
    (geometricTrack f g) (normalizationTrack f g) (sourceUnitTrack f g r)
    (middleUnitTrack f g r) (finalUnitTrack f g r)
    (geometricPasting f g r) (normalizationPasting f g r)
    (geometricPasting_lift f g r) (normalizationPasting_lift f g r)

end Quillen.PerfectComplexes.UnitTrackPostcompSimplex
