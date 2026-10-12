/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.CompositionHomotopyNaturality
public import Quillen.Waldhausen.SConstruction.Iterated.EndotransformationContraction
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopyNaturality
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumTransformationTransport

/-!
# Naturality of the original endotransformation contraction

Chosen-zero preservation and the universal properties of the actual zero objects identify the
original zero endotransformation under strict exact whiskering. The composition triangle and
uniform time operations then identify the existing cancellation expression pointwise. No new
contraction is chosen. Both homotopy times remain independent; degree zero retains its original
based-loop coordinate through the imported whole-level naturality statements.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u

/-- Exact heterogeneous equality of the original generic Eq.mp transport. -/
private theorem original_mp_heq {α β : Sort u} (e : α = β) (x : α) :
    HEq (Eq.mp e x) x := by
  cases e
  rfl

namespace Quillen.LoopPrespectrum

/- The following private lemmas concern evaluation of existing operations. In particular,
   the cast lemma removes only endpoint-index transport, never either time coordinate. -/

private theorem comparison_apply_eq_of_heq {E B : LoopPrespectrum.{u}}
    {f g : E ⟶ B} {H K H' K' : Homotopy f g}
    (hH : H = H') (hK : K = K') (J : H.RelHomotopy K) (J' : H'.RelHomotopy K')
    (he : HEq J J') (n : ℕ) (r s : unitInterval) (x : E.space n) :
    J.level n (r, (s, x)) = J'.level n (r, (s, x)) := by
  subst hH
  subst hK
  cases he
  rfl

private theorem comparison_cast_apply {E B : LoopPrespectrum.{u}} {f g : E ⟶ B}
    {H K H' K' : Homotopy f g} (hH : H = H') (hK : K = K')
    (e : H.RelHomotopy K = H'.RelHomotopy K') (J : H.RelHomotopy K)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (cast e J).level n (r, (s, x)) = J.level n (r, (s, x)) := by
  subst hH
  subst hK
  rfl

private theorem transRefl_eq_reparam {E B : LoopPrespectrum.{u}} {f g : E ⟶ B}
    (H : Homotopy f g) :
    H.trans (Homotopy.refl g) = H.reparam
      ⟨fun s ↦ ⟨Path.Homotopy.transReflReparamAux s,
        Path.Homotopy.transReflReparamAux_mem_I s⟩, by fun_prop⟩
      (Subtype.ext Path.Homotopy.transReflReparamAux_zero)
      (Subtype.ext Path.Homotopy.transReflReparamAux_one) := by
  apply Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  have hp := Path.Homotopy.trans_refl_reparam (H.path n x)
  rw [← Homotopy.path_refl g n x, ← Homotopy.path_trans] at hp
  exact DFunLike.congr_fun hp s

private theorem transAssoc_eq_reparam {E B : LoopPrespectrum.{u}} {f g h k : E ⟶ B}
    (H : Homotopy f g) (K : Homotopy g h) (L : Homotopy h k) :
    (H.trans K).trans L = (H.trans (K.trans L)).reparam
      ⟨fun s ↦ ⟨Path.Homotopy.transAssocReparamAux s,
        Path.Homotopy.transAssocReparamAux_mem_I s⟩, by fun_prop⟩
      (Subtype.ext Path.Homotopy.transAssocReparamAux_zero)
      (Subtype.ext Path.Homotopy.transAssocReparamAux_one) := by
  apply Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  have hp := Path.Homotopy.trans_assoc_reparam (H.path n x) (K.path n x) (L.path n x)
  simp only [← Homotopy.path_trans] at hp
  exact DFunLike.congr_fun hp s

section Evaluation
variable {E B E' B' : LoopPrespectrum.{u}}
  {f g h k : E ⟶ B} {f' g' h' k' : E' ⟶ B'}
  {n : ℕ} {x : E.space n} {x' : E'.space n} {p : B.space n → B'.space n}

private theorem track_trans_natural
    {H : Homotopy f g} {K : Homotopy g h}
    {H' : Homotopy f' g'} {K' : Homotopy g' h'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x)))
    (hK : ∀ s, K'.level n (s, x') = p (K.level n (s, x))) :
    ∀ s, (H'.trans K').level n (s, x') = p ((H.trans K).level n (s, x)) := by
  intro s
  change ((H'.levelHomotopy n).trans (K'.levelHomotopy n)) (s, x') =
    p (((H.levelHomotopy n).trans (K.levelHomotopy n)) (s, x))
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact hH _
  · exact hK _

private theorem track_symm_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ s, H'.symm.level n (s, x') = p (H.symm.level n (s, x)) :=
  fun s ↦ hH (unitInterval.symm s)

private theorem comparison_refl_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ r s, (Homotopy.RelHomotopy.refl H').level n (r, (s, x')) =
      p ((Homotopy.RelHomotopy.refl H).level n (r, (s, x))) := fun _ s ↦ hH s

private theorem comparison_symm_natural
    {H K : Homotopy f g} {H' K' : Homotopy f' g'}
    {J : H.RelHomotopy K} {J' : H'.RelHomotopy K'}
    (hJ : ∀ r s, J'.level n (r, (s, x')) = p (J.level n (r, (s, x)))) :
    ∀ r s, J'.symm.level n (r, (s, x')) = p (J.symm.level n (r, (s, x))) :=
  fun r s ↦ hJ (unitInterval.symm r) s

private theorem comparison_trans_natural
    {H K L : Homotopy f g} {H' K' L' : Homotopy f' g'}
    {J : H.RelHomotopy K} {M : K.RelHomotopy L}
    {J' : H'.RelHomotopy K'} {M' : K'.RelHomotopy L'}
    (hJ : ∀ r s, J'.level n (r, (s, x')) = p (J.level n (r, (s, x))))
    (hM : ∀ r s, M'.level n (r, (s, x')) = p (M.level n (r, (s, x)))) :
    ∀ r s, (J'.trans M').level n (r, (s, x')) =
      p ((J.trans M).level n (r, (s, x))) := by
  intro r s
  change ((J'.level n).trans (M'.level n)) (r, (s, x')) =
    p (((J.level n).trans (M.level n)) (r, (s, x)))
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact hJ _ s
  · exact hM _ s

private theorem comparison_hcomp_natural
    {H K : Homotopy f g} {L M : Homotopy g h}
    {H' K' : Homotopy f' g'} {L' M' : Homotopy g' h'}
    {J : H.RelHomotopy K} {N : L.RelHomotopy M}
    {J' : H'.RelHomotopy K'} {N' : L'.RelHomotopy M'}
    (hJ : ∀ r s, J'.level n (r, (s, x')) = p (J.level n (r, (s, x))))
    (hN : ∀ r s, N'.level n (r, (s, x')) = p (N.level n (r, (s, x)))) :
    ∀ r s, (J'.hcomp N').level n (r, (s, x')) =
      p ((J.hcomp N).level n (r, (s, x))) := by
  intro r s
  unfold Homotopy.RelHomotopy.hcomp
  change (ContinuousMap.Homotopy.trans _ _) (s, (r, x')) =
    p ((ContinuousMap.Homotopy.trans _ _) (s, (r, x)))
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split
  · exact hJ r _
  · exact hN r _

private theorem comparison_transRefl_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ r s, (Homotopy.RelHomotopy.transRefl H').level n (r, (s, x')) =
      p ((Homotopy.RelHomotopy.transRefl H).level n (r, (s, x))) := by
  intro r s
  unfold Homotopy.RelHomotopy.transRefl
  simp only [eq_mp_eq_cast, comparison_cast_apply, transRefl_eq_reparam]
  exact hH _

private theorem comparison_transAssoc_natural
    {H : Homotopy f g} {K : Homotopy g h} {L : Homotopy h k}
    {H' : Homotopy f' g'} {K' : Homotopy g' h'} {L' : Homotopy h' k'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x)))
    (hK : ∀ s, K'.level n (s, x') = p (K.level n (s, x)))
    (hL : ∀ s, L'.level n (s, x') = p (L.level n (s, x))) :
    ∀ r s, (Homotopy.RelHomotopy.transAssoc H' K' L').level n (r, (s, x')) =
      p ((Homotopy.RelHomotopy.transAssoc H K L).level n (r, (s, x))) := by
  intro r s
  have hT := track_trans_natural hH (track_trans_natural hK hL)
  unfold Homotopy.RelHomotopy.transAssoc
  simp only [eq_mp_eq_cast, comparison_cast_apply, transAssoc_eq_reparam]
  exact hT _

private theorem comparison_reflTransSymm_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ r s, (Homotopy.RelHomotopy.reflTransSymm H').level n (r, (s, x')) =
      p ((Homotopy.RelHomotopy.reflTransSymm H).level n (r, (s, x))) := by
  intro r s
  exact hH _

end Evaluation
end Quillen.LoopPrespectrum

namespace Quillen.Waldhausen.IteratedS

variable {V W T : Model.{u}} (F : V ⟶ W)

/-- Mapping the two original arrows through the chosen zero gives the same zero endomorphism. -/
theorem modelZeroEndotransformation_postcomp (J : W ⟶ T) :
    whiskerRight (modelZeroEndotransformation F) J.functor =
      modelZeroEndotransformation (F ≫ J) := by
  ext A
  change J.functor.map (W.waldhausen.isZero.from_ (F.functor.obj A) ≫
    W.waldhausen.isZero.to_ (F.functor.obj A)) =
      T.waldhausen.isZero.from_ (J.functor.obj (F.functor.obj A)) ≫
        T.waldhausen.isZero.to_ (J.functor.obj (F.functor.obj A))
  have h₀ : J.functor.map (W.waldhausen.isZero.from_ (F.functor.obj A)) =
      T.waldhausen.isZero.from_ (J.functor.obj (F.functor.obj A)) ≫
        eqToHom J.zero.symm := (J.exact.zero W.waldhausen.isZero).eq_of_tgt _ _
  have h₁ : J.functor.map (W.waldhausen.isZero.to_ (F.functor.obj A)) =
      eqToHom J.zero ≫ T.waldhausen.isZero.to_ (J.functor.obj (F.functor.obj A)) :=
    (J.exact.zero W.waldhausen.isZero).eq_of_src _ _
  rw [Functor.map_comp, h₀, h₁]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- Prewhiskering retains the literal two-arrow factorization through the chosen target zero. -/
theorem modelZeroEndotransformation_precomp (J : T ⟶ V) :
    whiskerLeft J.functor (modelZeroEndotransformation F) =
      modelZeroEndotransformation (J ≫ F) := rfl

/-- Precomposition preserves weakness of the actual chosen zero endotransformation. -/
theorem modelZeroEndotransformation_precomp_weak
    (hz : ∀ A, W.waldhausen.weq
      ((modelZeroEndotransformation (V := V) (W := W) F).app A)) (J : T ⟶ V) :
    ∀ A : T, W.waldhausen.weq
      ((modelZeroEndotransformation (V := T) (W := W) (J ≫ F)).app A) := by
  intro A
  rw [← modelZeroEndotransformation_precomp F J]
  exact hz (J.functor.obj A)

/-- Exact postcomposition preserves weakness of the actual chosen-zero endotransformation. -/
theorem modelZeroEndotransformation_postcomp_weak
    (hz : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A)) (J : W ⟶ T) :
    ∀ A, T.waldhausen.weq ((modelZeroEndotransformation (F ≫ J)).app A) := by
  intro A
  rw [← modelZeroEndotransformation_postcomp F J]
  exact J.exact.weak _ (hz A)

/-- Equal original weak transformations retain their exact whole source track. -/
private theorem absorption_source_eq_via_levels
    (η : F.functor ⟶ F.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hz : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A)) :
    prespectrumTransformationHomotopy (F := F) (G := F)
      (η ≫ modelZeroEndotransformation F)
      (fun A ↦ W.waldhausen.weq.comp_mem _ _ (hη A) (hz A)) =
    prespectrumTransformationHomotopy (F := F) (G := F)
      (modelZeroEndotransformation F) hz := by
  apply Quillen.LoopPrespectrum.Homotopy.ext
  funext m
  exact prespectrumTransformationHomotopy_level_eq_of_heq
    (F := F) (F' := F) (G := F) (G' := F) rfl rfl
    (η ≫ modelZeroEndotransformation F) (modelZeroEndotransformation F)
    (fun A ↦ W.waldhausen.weq.comp_mem _ _ (hη A) (hz A)) hz
    (heq_of_eq (modelZeroEndotransformation_absorb F η)) m

/-- The original absorption triangle is the actual endpoint cast of its original comparison. -/
private theorem absorption_heq_via_delta_mp_explicit
    (η : F.functor ⟶ F.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hz : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A)) :
    HEq (prespectrumEndotransformationAbsorptionTriangle F η hη hz)
      (prespectrumTransformationCompositionHomotopy (F := F) (G := F) (H := F) η
        (modelZeroEndotransformation F) hη hz) := by
  delta prespectrumEndotransformationAbsorptionTriangle
  exact original_mp_heq
    (α := (prespectrumTransformationHomotopy (F := F) (G := F)
      (η ≫ modelZeroEndotransformation F)
      (fun A ↦ W.waldhausen.weq.comp_mem _ _ (hη A) (hz A))).RelHomotopy
        ((prespectrumTransformationHomotopy (F := F) (G := F) η hη).trans
          (prespectrumTransformationHomotopy (F := F) (G := F)
            (modelZeroEndotransformation F) hz)))
    (β := (prespectrumTransformationHomotopy (F := F) (G := F)
      (modelZeroEndotransformation F) hz).RelHomotopy
        ((prespectrumTransformationHomotopy (F := F) (G := F) η hη).trans
          (prespectrumTransformationHomotopy (F := F) (G := F)
            (modelZeroEndotransformation F) hz)))
    _ (prespectrumTransformationCompositionHomotopy (F := F) (G := F) (H := F) η
      (modelZeroEndotransformation F) hη hz)

/-- The absorption identification changes no point of the original composition triangle. -/
theorem prespectrumEndotransformationAbsorptionTriangle_apply
    (η : F.functor ⟶ F.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hz : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationAbsorptionTriangle F η hη hz).level n (r, (s, x)) =
      (prespectrumTransformationCompositionHomotopy (F := F) (G := F) (H := F) η
        (modelZeroEndotransformation F) hη hz).level n (r, (s, x)) := by
  exact Quillen.LoopPrespectrum.comparison_apply_eq_of_heq
    (E := prespectrum V) (B := prespectrum W)
    (f := prespectrumMap F) (g := prespectrumMap F)
    (H := prespectrumTransformationHomotopy (F := F) (G := F)
      (modelZeroEndotransformation F) hz)
    (H' := prespectrumTransformationHomotopy (F := F) (G := F)
      (η ≫ modelZeroEndotransformation F)
      (fun A ↦ W.waldhausen.weq.comp_mem _ _ (hη A) (hz A)))
    (K := (prespectrumTransformationHomotopy (F := F) (G := F) η hη).trans
      (prespectrumTransformationHomotopy (F := F) (G := F)
        (modelZeroEndotransformation F) hz))
    (K' := (prespectrumTransformationHomotopy (F := F) (G := F) η hη).trans
      (prespectrumTransformationHomotopy (F := F) (G := F)
        (modelZeroEndotransformation F) hz))
    (absorption_source_eq_via_levels F η hη hz).symm rfl
    (prespectrumEndotransformationAbsorptionTriangle F η hη hz)
    (prespectrumTransformationCompositionHomotopy (F := F) (G := F) (H := F) η
      (modelZeroEndotransformation F) hη hz)
    (absorption_heq_via_delta_mp_explicit F η hη hz) n r s x

/-- Equality of the actual second transformation preserves its original triangle at every point. -/
private theorem composition_point_eq_of_eq
    {V' W' : Model.{u}} {F' G' H' : V' ⟶ W'}
    (η : F'.functor ⟶ G'.functor) (θ θ' : G'.functor ⟶ H'.functor)
    (hη : ∀ A, W'.waldhausen.weq (η.app A))
    (hθ : ∀ A, W'.waldhausen.weq (θ.app A))
    (hθ' : ∀ A, W'.waldhausen.weq (θ'.app A)) (he : θ = θ')
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V').space n) :
    (prespectrumTransformationCompositionHomotopy (F := F') (G := G') (H := H')
      η θ hη hθ).level n (r, (s, x)) =
    (prespectrumTransformationCompositionHomotopy (F := F') (G := G') (H := H')
      η θ' hη hθ').level n (r, (s, x)) := by
  subst θ'
  rfl

/-- The original absorption triangle commutes with exact postcomposition at both times. -/
theorem prespectrumEndotransformationAbsorptionTriangle_postcomp_level
    (η : F.functor ⟶ F.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hz : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A)) (J : W ⟶ T)
    (hz' : ∀ A, T.waldhausen.weq ((modelZeroEndotransformation (F ≫ J)).app A))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationAbsorptionTriangle (F ≫ J) (whiskerRight η J.functor)
      (fun A ↦ J.exact.weak _ (hη A)) hz').level n (r, (s, x)) =
      (prespectrumMap J).map n
        ((prespectrumEndotransformationAbsorptionTriangle F η hη hz).level n (r, (s, x))) := by
  rw [prespectrumEndotransformationAbsorptionTriangle_apply,
    prespectrumEndotransformationAbsorptionTriangle_apply]
  have hpoint := composition_point_eq_of_eq
    (F' := F ≫ J) (G' := F ≫ J) (H' := F ≫ J)
    (whiskerRight η J.functor)
    (whiskerRight (modelZeroEndotransformation F) J.functor)
    (modelZeroEndotransformation (F ≫ J))
    (fun A ↦ J.exact.weak _ (hη A)) (fun A ↦ J.exact.weak _ (hz A)) hz'
    (modelZeroEndotransformation_postcomp F J) n r s x
  exact hpoint.symm.trans
    (prespectrumTransformationCompositionHomotopy_postcomp_level
      (F := F) (G := F) (H := F) η (modelZeroEndotransformation F) hη hz J n r s x)

/-- The original absorption triangle commutes with exact precomposition at both times. -/
theorem prespectrumEndotransformationAbsorptionTriangle_precomp_level
    (η : F.functor ⟶ F.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hz : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A)) (J : T ⟶ V)
    (n : ℕ) (r s : unitInterval) (x : (prespectrum T).space n) :
    (prespectrumEndotransformationAbsorptionTriangle (J ≫ F) (whiskerLeft J.functor η)
      (fun A ↦ hη (J.functor.obj A)) (fun A ↦ hz (J.functor.obj A))).level n (r, (s, x)) =
      (prespectrumEndotransformationAbsorptionTriangle F η hη hz).level n
        (r, (s, (prespectrumMap J).map n x)) := by
  rw [prespectrumEndotransformationAbsorptionTriangle_apply,
    prespectrumEndotransformationAbsorptionTriangle_apply]
  exact prespectrumTransformationCompositionHomotopy_precomp_level
    (F := F) (G := F) (H := F) η
    (modelZeroEndotransformation F) hη hz J n r s x

section CancellationEvaluation
variable {V' W' : Model.{u}} {F' : V' ⟶ W'}
  {η : F.functor ⟶ F.functor} {η' : F'.functor ⟶ F'.functor}
  {hη : ∀ A, W.waldhausen.weq (η.app A)} {hη' : ∀ A, W'.waldhausen.weq (η'.app A)}
  {hz : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A)}
  {hz' : ∀ A, W'.waldhausen.weq ((modelZeroEndotransformation F').app A)}

/-- Pointwise compatibility propagates through the unchanged original cancellation expression. -/
private theorem contraction_evaluation_natural
    {n : ℕ} {x : (prespectrum V).space n} {x' : (prespectrum V').space n}
    {p : (prespectrum W).space n → (prespectrum W').space n}
    (hH : ∀ s, (prespectrumTransformationHomotopy (F := F') (G := F') η' hη').level n (s, x') =
      p ((prespectrumTransformationHomotopy (F := F) (G := F) η hη).level n (s, x)))
    (hZ : ∀ s, (prespectrumTransformationHomotopy (F := F') (G := F')
      (modelZeroEndotransformation F') hz').level n
      (s, x') = p ((prespectrumTransformationHomotopy (F := F) (G := F)
        (modelZeroEndotransformation F) hz).level n (s, x)))
    (hJ : ∀ r s, (prespectrumEndotransformationAbsorptionTriangle F' η' hη' hz').level n
      (r, (s, x')) =
      p ((prespectrumEndotransformationAbsorptionTriangle F η hη hz).level n (r, (s, x)))) :
    ∀ r s, (prespectrumEndotransformationContraction F' η' hη' hz').level n (r, (s, x')) =
      p ((prespectrumEndotransformationContraction F η hη hz).level n (r, (s, x))) := by
  unfold prespectrumEndotransformationContraction
  apply comparison_trans_natural
  · exact comparison_symm_natural (comparison_transRefl_natural hH)
  · apply comparison_trans_natural
    · exact comparison_hcomp_natural (comparison_refl_natural hH)
        (comparison_reflTransSymm_natural hZ)
    · apply comparison_trans_natural
      · exact comparison_symm_natural
          (comparison_transAssoc_natural hH hZ (track_symm_natural hZ))
      · apply comparison_trans_natural
        · exact comparison_hcomp_natural (comparison_symm_natural hJ)
            (comparison_refl_natural (track_symm_natural hZ))
        · exact comparison_symm_natural (comparison_reflTransSymm_natural hZ)

end CancellationEvaluation

/-- Exact postcomposition preserves the specified original contraction at all levels and times.
The target weak-zero witness is arbitrary, so this applies to the canonical transported witness. -/
theorem prespectrumEndotransformationContraction_postcomp_level
    (η : F.functor ⟶ F.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hz : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A)) (J : W ⟶ T)
    (hz' : ∀ A, T.waldhausen.weq ((modelZeroEndotransformation (F ≫ J)).app A))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction (F ≫ J) (whiskerRight η J.functor)
      (fun A ↦ J.exact.weak _ (hη A)) hz').level n (r, (s, x)) =
      (prespectrumMap J).map n
        ((prespectrumEndotransformationContraction F η hη hz).level n (r, (s, x))) := by
  refine contraction_evaluation_natural F
    (F' := F ≫ J) (η := η) (η' := whiskerRight η J.functor)
    (hη := hη) (hη' := fun A ↦ J.exact.weak _ (hη A))
    (hz := hz) (hz' := hz') (n := n) (x := x) (x' := x)
    (p := (prespectrumMap J).map n) ?_ ?_ ?_ r s
  · intro t
    exact congrArg (fun K ↦ K (t, x))
      (prespectrumTransformationHomotopy_postcomp_level (F := F) (G := F) η hη J n)
  · intro t
    have he := prespectrumTransformationHomotopy_level_eq_of_heq
      (F := F ≫ J) (F' := F ≫ J) (G := F ≫ J) (G' := F ≫ J) rfl rfl
      (whiskerRight (modelZeroEndotransformation F) J.functor)
      (modelZeroEndotransformation (F ≫ J))
      (fun A ↦ J.exact.weak _ (hz A)) hz'
      (heq_of_eq (modelZeroEndotransformation_postcomp F J)) n
    have hZ := congrArg (fun K ↦ K (t, x))
      (prespectrumTransformationHomotopy_postcomp_level
        (F := F) (G := F) (modelZeroEndotransformation F) hz J n)
    exact (congrArg (fun K ↦ K (t, x)) he).symm.trans hZ
  · exact fun a b ↦
      prespectrumEndotransformationAbsorptionTriangle_postcomp_level F η hη hz J hz' n a b x


/-- Equal original transformations retain the same chosen contraction at both times. -/
theorem prespectrumEndotransformationContraction_level_eq_of_heq
    {V W : Model.{u}} {F F' : V ⟶ W} (h : F = F')
    (η : F.functor ⟶ F.functor) (η' : F'.functor ⟶ F'.functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X))
    (hη' : ∀ X, W.waldhausen.weq (η'.app X))
    (hz : ∀ X, W.waldhausen.weq ((modelZeroEndotransformation F).app X))
    (hz' : ∀ X, W.waldhausen.weq ((modelZeroEndotransformation F').app X))
    (he : HEq η η') (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction F η hη hz).level n (r, (s, x)) =
      (prespectrumEndotransformationContraction F' η' hη' hz').level n (r, (s, x)) := by
  cases h
  have hηeq : η = η' := eq_of_heq he
  cases hηeq
  have hw : hη = hη' := Subsingleton.elim _ _
  cases hw
  have hwz : hz = hz' := Subsingleton.elim _ _
  cases hwz
  rfl

/-- Point evaluation of the unchanged whole precomposition equation. -/
private theorem originalPrecompositionTrack_apply
    (η : F.functor ⟶ F.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))
    (J : T ⟶ V) (n : ℕ) (s : unitInterval) (x : (prespectrum T).space n) :
    (prespectrumTransformationHomotopy (F := J ≫ F) (G := J ≫ F)
      (whiskerLeft J.functor η) (fun A ↦ hη (J.functor.obj A))).level n (s, x) =
    (prespectrumTransformationHomotopy (F := F) (G := F) η hη).level n
      (s, (prespectrumMap (V := T) (W := V) J).map n x) := by
  exact congrArg
    (fun K : C(unitInterval × (prespectrum T).space n, (prespectrum W).space n) ↦ K (s, x))
    (prespectrumTransformationHomotopy_precomp_level (F := F) (G := F) η hη J n)

/-- The original zero self-track precomposes at every original time. -/
private theorem originalZeroPrecompositionTrack_apply
    (hz : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A))
    (J : T ⟶ V) (n : ℕ) (s : unitInterval) (x : (prespectrum T).space n) :
    (prespectrumTransformationHomotopy (F := J ≫ F) (G := J ≫ F)
      (modelZeroEndotransformation (V := T) (W := W) (J ≫ F))
      (modelZeroEndotransformation_precomp_weak F hz J)).level n (s, x) =
    (prespectrumTransformationHomotopy (F := F) (G := F)
      (modelZeroEndotransformation F) hz).level n
      (s, (prespectrumMap (V := T) (W := V) J).map n x) := by
  have he := prespectrumTransformationHomotopy_level_eq_of_heq
    (F := J ≫ F) (F' := J ≫ F) (G := J ≫ F) (G' := J ≫ F) rfl rfl
    (whiskerLeft J.functor (modelZeroEndotransformation F))
    (modelZeroEndotransformation (V := T) (W := W) (J ≫ F))
    (fun A ↦ hz (J.functor.obj A)) (modelZeroEndotransformation_precomp_weak F hz J)
    (heq_of_eq (modelZeroEndotransformation_precomp F J)) n
  have hpoint := congrArg
    (fun K : C(unitInterval × (prespectrum T).space n, (prespectrum W).space n) ↦ K (s, x)) he
  exact hpoint.symm.trans
    (originalPrecompositionTrack_apply F (modelZeroEndotransformation F) hz J n s x)

/-- Proof-irrelevant weakness witnesses retain every value of the same chosen triangle. -/
private theorem absorptionWeakWitness_apply
    (η : F.functor ⟶ F.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hz hz' : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationAbsorptionTriangle (V := V) (W := W)
      F η hη hz).level n (r, (s, x)) =
    (prespectrumEndotransformationAbsorptionTriangle (V := V) (W := W)
      F η hη hz').level n (r, (s, x)) := by
  have h : hz = hz' := Subsingleton.elim _ _
  cases h
  rfl

/-- Both original absorption times retain the same triangle after precomposition. -/
private theorem originalAbsorptionPrecomposition_apply
    (η : F.functor ⟶ F.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hz : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A))
    (J : T ⟶ V) (n : ℕ) (r s : unitInterval) (x : (prespectrum T).space n) :
    (prespectrumEndotransformationAbsorptionTriangle (V := T) (W := W)
      (J ≫ F) (whiskerLeft J.functor η) (fun A ↦ hη (J.functor.obj A))
      (modelZeroEndotransformation_precomp_weak F hz J)).level n (r, (s, x)) =
    (prespectrumEndotransformationAbsorptionTriangle (V := V) (W := W)
      F η hη hz).level n (r, (s, (prespectrumMap (V := T) (W := V) J).map n x)) := by
  have hpoint := absorptionWeakWitness_apply (V := T) (W := W)
    (J ≫ F) (whiskerLeft J.functor η) (fun A ↦ hη (J.functor.obj A))
    (modelZeroEndotransformation_precomp_weak F hz J) (fun A ↦ hz (J.functor.obj A))
    n r s x
  exact hpoint.trans
    (prespectrumEndotransformationAbsorptionTriangle_precomp_level
      (V := V) (W := W) (T := T) F η hη hz J n r s x)

/-- Exact precomposition preserves the specified original contraction at all levels and times. -/
private theorem contraction_precomp_named_weak
    (η : F.functor ⟶ F.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hz : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A)) (J : T ⟶ V)
    (n : ℕ) (r s : unitInterval) (x : (prespectrum T).space n) :
    (prespectrumEndotransformationContraction (V := T) (W := W) (J ≫ F) (whiskerLeft J.functor η)
      (fun A ↦ hη (J.functor.obj A)) (modelZeroEndotransformation_precomp_weak F hz J)).level n
        (r, (s, x)) =
      (prespectrumEndotransformationContraction (V := V) (W := W) F η hη hz).level n
        (r, (s, (prespectrumMap (V := T) (W := V) J).map n x)) := by
  exact contraction_evaluation_natural (V := V) (W := W) (V' := T) (W' := W) F
    (F' := J ≫ F) (η := η) (η' := whiskerLeft J.functor η)
    (hη := hη) (hη' := fun A ↦ hη (J.functor.obj A))
    (hz := hz) (hz' := modelZeroEndotransformation_precomp_weak F hz J)
    (n := n) (x := (prespectrumMap (V := T) (W := V) J).map n x)
    (x' := x) (p := fun y : (prespectrum W).space n ↦ y)
    (fun t ↦ originalPrecompositionTrack_apply (V := V) (W := W) (T := T) F η hη J n t x)
    (fun t ↦ originalZeroPrecompositionTrack_apply (V := V) (W := W) (T := T) F hz J n t x)
    (fun a b ↦ originalAbsorptionPrecomposition_apply
      (V := V) (W := W) (T := T) F η hη hz J n a b x) r s

/-- Exact precomposition preserves the specified original contraction at all levels and times. -/
theorem prespectrumEndotransformationContraction_precomp_level
    (η : F.functor ⟶ F.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hz : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A)) (J : T ⟶ V)
    (n : ℕ) (r s : unitInterval) (x : (prespectrum T).space n) :
    (prespectrumEndotransformationContraction (J ≫ F) (whiskerLeft J.functor η)
      (fun A ↦ hη (J.functor.obj A)) (fun A ↦ hz (J.functor.obj A))).level n (r, (s, x)) =
      (prespectrumEndotransformationContraction F η hη hz).level n
        (r, (s, (prespectrumMap J).map n x)) := by
  have hc := prespectrumEndotransformationContraction_level_eq_of_heq
    (V := T) (W := W) (F := J ≫ F) (F' := J ≫ F) rfl
    (whiskerLeft J.functor η) (whiskerLeft J.functor η)
    (fun A ↦ hη (J.functor.obj A)) (fun A ↦ hη (J.functor.obj A))
    (fun A ↦ hz (J.functor.obj A)) (modelZeroEndotransformation_precomp_weak F hz J)
    (HEq.rfl) n r s x
  exact hc.trans (contraction_precomp_named_weak F η hη hz J n r s x)

/-- The postcomposed original contraction retains the independent structure parameter. -/
theorem prespectrumEndotransformationContraction_postcomp_structure
    (η : F.functor ⟶ F.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hz : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A)) (J : W ⟶ T)
    (hz' : ∀ A, T.waldhausen.weq ((modelZeroEndotransformation (F ≫ J)).app A))
    (n : ℕ) (r s t : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction (F ≫ J) (whiskerRight η J.functor)
      (fun A ↦ J.exact.weak _ (hη A)) hz').level (n + 1)
        (r, (s, (prespectrum V).structureMap n x t)) =
      (prespectrum T).structureMap n ((prespectrumMap J).map n
        ((prespectrumEndotransformationContraction F η hη hz).level n (r, (s, x)))) t := by
  rw [prespectrumEndotransformationContraction_postcomp_level F η hη hz J hz',
    (prespectrumEndotransformationContraction F η hη hz).comm]
  exact congrArg (fun γ ↦ γ t) ((prespectrumMap J).comm n
    ((prespectrumEndotransformationContraction F η hη hz).level n (r, (s, x))))

/-- The precomposed original contraction retains the independent structure parameter. -/
theorem prespectrumEndotransformationContraction_precomp_structure
    (η : F.functor ⟶ F.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hz : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A)) (J : T ⟶ V)
    (n : ℕ) (r s t : unitInterval) (x : (prespectrum T).space n) :
    (prespectrumEndotransformationContraction (J ≫ F) (whiskerLeft J.functor η)
      (fun A ↦ hη (J.functor.obj A)) (fun A ↦ hz (J.functor.obj A))).level (n + 1)
        (r, (s, (prespectrum T).structureMap n x t)) =
      (prespectrum W).structureMap n
        ((prespectrumEndotransformationContraction F η hη hz).level n
          (r, (s, (prespectrumMap J).map n x))) t := by
  rw [(prespectrumEndotransformationContraction (J ≫ F) (whiskerLeft J.functor η)
    (fun A ↦ hη (J.functor.obj A)) (fun A ↦ hz (J.functor.obj A))).comm]
  rw [prespectrumEndotransformationContraction_precomp_level F η hη hz J]

/-- At degree zero, the original internal loop coordinate is separate from both times. -/
theorem prespectrumEndotransformationContraction_postcomp_zero_apply
    (η : F.functor ⟶ F.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hz : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A)) (J : W ⟶ T)
    (hz' : ∀ A, T.waldhausen.weq ((modelZeroEndotransformation (F ≫ J)).app A))
    (r s q : unitInterval) (γ : Path (stagePoint 0 V) (stagePoint 0 V)) :
    (show Path (stagePoint 0 T) (stagePoint 0 T) from
      (prespectrumEndotransformationContraction (F ≫ J) (whiskerRight η J.functor)
        (fun A ↦ J.exact.weak _ (hη A)) hz').level 0 (r, (s, γ))) q =
      SSet.toTop.map ((stages 0).map J)
        ((show Path (stagePoint 0 W) (stagePoint 0 W) from
          (prespectrumEndotransformationContraction F η hη hz).level 0 (r, (s, γ))) q) :=
  congrArg (fun p : Path (stagePoint 0 T) (stagePoint 0 T) ↦ p q)
    (prespectrumEndotransformationContraction_postcomp_level F η hη hz J hz' 0 r s γ)

/-- Precomposition at degree zero retains the same independent internal loop coordinate. -/
theorem prespectrumEndotransformationContraction_precomp_zero_apply
    (η : F.functor ⟶ F.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hz : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A)) (J : T ⟶ V)
    (r s q : unitInterval) (γ : Path (stagePoint 0 T) (stagePoint 0 T)) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from
      (prespectrumEndotransformationContraction (J ≫ F) (whiskerLeft J.functor η)
        (fun A ↦ hη (J.functor.obj A)) (fun A ↦ hz (J.functor.obj A))).level 0
          (r, (s, γ))) q =
      (show Path (stagePoint 0 W) (stagePoint 0 W) from
        (prespectrumEndotransformationContraction F η hη hz).level 0
          (r, (s, (prespectrumMap J).map 0 γ))) q :=
  congrArg (fun p : Path (stagePoint 0 W) (stagePoint 0 W) ↦ p q)
    (prespectrumEndotransformationContraction_precomp_level F η hη hz J 0 r s γ)

/-- Equality-induced conjugation changes no value of the prescribed original contraction. -/
theorem prespectrumEndotransformationContraction_transport_level
    {V W : Model.{u}} {F F' : V ⟶ W} (h : F = F')
    (η : F'.functor ⟶ F'.functor) (hη : ∀ X, W.waldhausen.weq (η.app X))
    (hη' : ∀ X, W.waldhausen.weq
      ((eqToHom (congrArg Model.Hom.functor h) ≫ η ≫
        eqToHom (congrArg Model.Hom.functor h.symm)).app X))
    (hz : ∀ X, W.waldhausen.weq ((modelZeroEndotransformation F).app X))
    (hz' : ∀ X, W.waldhausen.weq ((modelZeroEndotransformation F').app X))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction F
      (eqToHom (congrArg Model.Hom.functor h) ≫ η ≫
        eqToHom (congrArg Model.Hom.functor h.symm)) hη' hz).level n (r, (s, x)) =
      (prespectrumEndotransformationContraction F' η hη hz').level n (r, (s, x)) := by
  have he : HEq
      (eqToHom (congrArg Model.Hom.functor h) ≫ η ≫
        eqToHom (congrArg Model.Hom.functor h.symm)) η := by
    cases h
    exact heq_of_eq (by simp only [eqToHom_refl, Category.id_comp, Category.comp_id])
  exact prespectrumEndotransformationContraction_level_eq_of_heq
    (V := V) (W := W) (F := F) (F' := F') h
    (eqToHom (congrArg Model.Hom.functor h) ≫ η ≫
      eqToHom (congrArg Model.Hom.functor h.symm)) η hη' hη hz hz' he n r s x

/-- The original scalar square transfers exactly the original weakness witness. -/
private theorem originalCoefficientConjugate_weak
    {V W T U : Model.{u}} (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (h : F ≫ b = a ≫ G)
    (η : F.functor ⟶ F.functor) (θ : G.functor ⟶ G.functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X))
    (he : whiskerRight η b.functor =
      eqToHom (congrArg Model.Hom.functor h) ≫ whiskerLeft a.functor θ ≫
        eqToHom (congrArg Model.Hom.functor h.symm)) :
    ∀ X, U.waldhausen.weq
      ((eqToHom (congrArg Model.Hom.functor h) ≫ whiskerLeft a.functor θ ≫
        eqToHom (congrArg Model.Hom.functor h.symm)).app X) := by
  intro X
  rw [← he]
  exact b.exact.weak _ (hη X)

/-- This is exactly the original prewhiskering, with its composite Model endpoint displayed. -/
private def coefficientPrewhiskerTyped {V T U : Model.{u}} (a : V ⟶ T) (G : T ⟶ U)
    (θ : G.functor ⟶ G.functor) : (a ≫ G).functor ⟶ (a ≫ G).functor :=
  whiskerLeft a.functor θ

/-- Naming the endpoint conversion changes no transformation. -/
private theorem coefficientPrewhiskerTyped_eq {V T U : Model.{u}} (a : V ⟶ T) (G : T ⟶ U)
    (θ : G.functor ⟶ G.functor) :
    coefficientPrewhiskerTyped a G θ = whiskerLeft a.functor θ := rfl

/-- The named transformation has the original component weakness witness. -/
private theorem coefficientPrewhiskerTyped_weak {V T U : Model.{u}} (a : V ⟶ T) (G : T ⟶ U)
    (θ : G.functor ⟶ G.functor) (hθ : ∀ X, U.waldhausen.weq (θ.app X)) :
    ∀ X, U.waldhausen.weq ((coefficientPrewhiskerTyped a G θ).app X) :=
  fun X ↦ hθ (a.functor.obj X)

/-- The same original coefficient square transfers weakness of the named transformation. -/
private theorem coefficientPrewhiskerTyped_conjugate_weak
    {V W T U : Model.{u}} (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (h : F ≫ b = a ≫ G)
    (η : F.functor ⟶ F.functor) (θ : G.functor ⟶ G.functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X))
    (he : whiskerRight η b.functor =
      eqToHom (congrArg Model.Hom.functor h) ≫ whiskerLeft a.functor θ ≫
        eqToHom (congrArg Model.Hom.functor h.symm)) :
    ∀ X, U.waldhausen.weq
      ((eqToHom (congrArg Model.Hom.functor h) ≫ coefficientPrewhiskerTyped a G θ ≫
        eqToHom (congrArg Model.Hom.functor h.symm)).app X) :=
  originalCoefficientConjugate_weak
    (V := V) (W := W) (T := T) (U := U) F G a b h η θ hη he

/-- This is exactly the original postwhiskering at the displayed Model composite. -/
private def coefficientPostwhiskerTyped {V W U : Model.{u}} (F : V ⟶ W) (b : W ⟶ U)
    (η : F.functor ⟶ F.functor) : (F ≫ b).functor ⟶ (F ≫ b).functor :=
  whiskerRight η b.functor

/-- Naming the endpoint conversion changes no transformation. -/
private theorem coefficientPostwhiskerTyped_eq {V W U : Model.{u}} (F : V ⟶ W) (b : W ⟶ U)
    (η : F.functor ⟶ F.functor) :
    coefficientPostwhiskerTyped F b η = whiskerRight η b.functor := rfl

/-- The named transformation retains the original exact-image weakness proof. -/
private theorem coefficientPostwhiskerTyped_weak {V W U : Model.{u}} (F : V ⟶ W) (b : W ⟶ U)
    (η : F.functor ⟶ F.functor) (hη : ∀ X, W.waldhausen.weq (η.app X)) :
    ∀ X, U.waldhausen.weq ((coefficientPostwhiskerTyped F b η).app X) :=
  fun X ↦ b.exact.weak _ (hη X)

/-- The original coefficient square is unchanged when its two endpoint conversions are named. -/
private theorem coefficientWhiskerTyped_square
    {V W T U : Model.{u}} (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (h : F ≫ b = a ≫ G)
    (η : F.functor ⟶ F.functor) (θ : G.functor ⟶ G.functor)
    (he : whiskerRight η b.functor =
      eqToHom (congrArg Model.Hom.functor h) ≫ whiskerLeft a.functor θ ≫
        eqToHom (congrArg Model.Hom.functor h.symm)) :
    coefficientPostwhiskerTyped (V := V) (W := W) (U := U) F b η =
      eqToHom (congrArg Model.Hom.functor h) ≫
        coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ ≫
          eqToHom (congrArg Model.Hom.functor h.symm) := he

/-- Actual coefficient transport, with the same original two composites and weak-zero proofs. -/
private theorem originalContractionCoefficientTransportTyped
    {V W T U : Model.{u}} (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (h : F ≫ b = a ≫ G)
    (η : F.functor ⟶ F.functor) (θ : G.functor ⟶ G.functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X))
    (hθ : ∀ X, U.waldhausen.weq (θ.app X))
    (hz : ∀ X, W.waldhausen.weq ((modelZeroEndotransformation F).app X))
    (hz' : ∀ X, U.waldhausen.weq ((modelZeroEndotransformation G).app X))
    (he : whiskerRight η b.functor =
      eqToHom (congrArg Model.Hom.functor h) ≫ whiskerLeft a.functor θ ≫
        eqToHom (congrArg Model.Hom.functor h.symm))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction (V := V) (W := U) (F ≫ b)
      (eqToHom (congrArg Model.Hom.functor h) ≫
        coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ ≫
        eqToHom (congrArg Model.Hom.functor h.symm))
      (coefficientPrewhiskerTyped_conjugate_weak
        (V := V) (W := W) (T := T) (U := U) F G a b h η θ hη he)
      (modelZeroEndotransformation_postcomp_weak
        (V := V) (W := W) (T := U) F hz b)).level n (r, (s, x)) =
    (prespectrumEndotransformationContraction (V := V) (W := U) (a ≫ G)
      (coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ)
      (coefficientPrewhiskerTyped_weak (V := V) (T := T) (U := U) a G θ hθ)
      (modelZeroEndotransformation_precomp_weak
        (V := T) (W := U) (T := V) G hz' a)).level n (r, (s, x)) :=
  prespectrumEndotransformationContraction_transport_level
    (V := V) (W := U) (F := F ≫ b) (F' := a ≫ G) h
    (coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ)
    (coefficientPrewhiskerTyped_weak (V := V) (T := T) (U := U) a G θ hθ)
    (coefficientPrewhiskerTyped_conjugate_weak
        (V := V) (W := W) (T := T) (U := U) F G a b h η θ hη he)
    (modelZeroEndotransformation_postcomp_weak
        (V := V) (W := W) (T := U) F hz b)
    (modelZeroEndotransformation_precomp_weak
        (V := T) (W := U) (T := V) G hz' a) n r s x

/-- The original scalar square compares the chosen contractions at identical independent times. -/
private theorem originalCoefficientEndotransformationEqTyped
    {V W T U : Model.{u}} (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (h : F ≫ b = a ≫ G)
    (η : F.functor ⟶ F.functor) (θ : G.functor ⟶ G.functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X))
    (hz : ∀ X, W.waldhausen.weq ((modelZeroEndotransformation F).app X))
    (he : whiskerRight η b.functor =
      eqToHom (congrArg Model.Hom.functor h) ≫ whiskerLeft a.functor θ ≫
        eqToHom (congrArg Model.Hom.functor h.symm))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction (V := V) (W := U) (F ≫ b)
      (coefficientPostwhiskerTyped (V := V) (W := W) (U := U) F b η)
      (coefficientPostwhiskerTyped_weak (V := V) (W := W) (U := U) F b η hη)
      (modelZeroEndotransformation_postcomp_weak
        (V := V) (W := W) (T := U) F hz b)).level n (r, (s, x)) =
    (prespectrumEndotransformationContraction (V := V) (W := U) (F ≫ b)
      (eqToHom (congrArg Model.Hom.functor h) ≫
        coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ ≫
          eqToHom (congrArg Model.Hom.functor h.symm))
      (coefficientPrewhiskerTyped_conjugate_weak
        (V := V) (W := W) (T := T) (U := U) F G a b h η θ hη he)
      (modelZeroEndotransformation_postcomp_weak
        (V := V) (W := W) (T := U) F hz b)).level n (r, (s, x)) :=
  prespectrumEndotransformationContraction_level_eq_of_heq
    (V := V) (W := U) (F := F ≫ b) (F' := F ≫ b) rfl
    (coefficientPostwhiskerTyped (V := V) (W := W) (U := U) F b η)
    (eqToHom (congrArg Model.Hom.functor h) ≫
      coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ ≫
        eqToHom (congrArg Model.Hom.functor h.symm))
    (coefficientPostwhiskerTyped_weak (V := V) (W := W) (U := U) F b η hη)
    (coefficientPrewhiskerTyped_conjugate_weak
      (V := V) (W := W) (T := T) (U := U) F G a b h η θ hη he)
    (modelZeroEndotransformation_postcomp_weak (V := V) (W := W) (T := U) F hz b)
    (modelZeroEndotransformation_postcomp_weak (V := V) (W := W) (T := U) F hz b)
    (heq_of_eq (coefficientWhiskerTyped_square
      (V := V) (W := W) (T := T) (U := U) F G a b h η θ he)) n r s x

/-- The typed postwhiskering retains the original postcomposition point at both times. -/
private theorem originalContractionPostTyped
    {V W U : Model.{u}} (F : V ⟶ W) (b : W ⟶ U)
    (η : F.functor ⟶ F.functor) (hη : ∀ X, W.waldhausen.weq (η.app X))
    (hz : ∀ X, W.waldhausen.weq ((modelZeroEndotransformation F).app X))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction (V := V) (W := U) (F ≫ b)
      (coefficientPostwhiskerTyped (V := V) (W := W) (U := U) F b η)
      (coefficientPostwhiskerTyped_weak (V := V) (W := W) (U := U) F b η hη)
      (modelZeroEndotransformation_postcomp_weak
        (V := V) (W := W) (T := U) F hz b)).level n (r, (s, x)) =
      (prespectrumMap (V := W) (W := U) b).map n
        ((prespectrumEndotransformationContraction F η hη hz).level n (r, (s, x))) := by
  have he := prespectrumEndotransformationContraction_level_eq_of_heq
    (V := V) (W := U) (F := F ≫ b) (F' := F ≫ b) rfl
    (coefficientPostwhiskerTyped (V := V) (W := W) (U := U) F b η)
    (whiskerRight η b.functor)
    (coefficientPostwhiskerTyped_weak (V := V) (W := W) (U := U) F b η hη)
    (fun X : V ↦ b.exact.weak _ (hη X))
    (modelZeroEndotransformation_postcomp_weak (V := V) (W := W) (T := U) F hz b)
    (modelZeroEndotransformation_postcomp_weak (V := V) (W := W) (T := U) F hz b)
    (heq_of_eq (coefficientPostwhiskerTyped_eq (V := V) (W := W) (U := U) F b η))
    n r s x
  exact he.trans (prespectrumEndotransformationContraction_postcomp_level
    (V := V) (W := W) (T := U) F η hη hz b
    (modelZeroEndotransformation_postcomp_weak (V := V) (W := W) (T := U) F hz b) n r s x)

/-- The typed prewhiskering retains the original precomposition point at both times. -/
private theorem originalContractionPreTyped
    {V T U : Model.{u}} (a : V ⟶ T) (G : T ⟶ U)
    (θ : G.functor ⟶ G.functor) (hθ : ∀ X, U.waldhausen.weq (θ.app X))
    (hz : ∀ X, U.waldhausen.weq ((modelZeroEndotransformation G).app X))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction (V := V) (W := U) (a ≫ G)
      (coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ)
      (coefficientPrewhiskerTyped_weak (V := V) (T := T) (U := U) a G θ hθ)
      (modelZeroEndotransformation_precomp_weak
        (V := T) (W := U) (T := V) G hz a)).level n (r, (s, x)) =
      (prespectrumEndotransformationContraction G θ hθ hz).level n
        (r, (s, (prespectrumMap (V := V) (W := T) a).map n x)) := by
  have he := prespectrumEndotransformationContraction_level_eq_of_heq
    (V := V) (W := U) (F := a ≫ G) (F' := a ≫ G) rfl
    (coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ)
    (whiskerLeft a.functor θ)
    (coefficientPrewhiskerTyped_weak (V := V) (T := T) (U := U) a G θ hθ)
    (fun X : V ↦ hθ (a.functor.obj X))
    (modelZeroEndotransformation_precomp_weak (V := T) (W := U) (T := V) G hz a)
    (fun X : V ↦ hz (a.functor.obj X))
    (heq_of_eq (coefficientPrewhiskerTyped_eq (V := V) (T := T) (U := U) a G θ)) n r s x
  exact he.trans (prespectrumEndotransformationContraction_precomp_level
    (V := T) (W := U) (T := V) G θ hθ hz a n r s x)

/-- The original strict coefficient square and scalar equation preserve the same contraction.
All equality-induced transports and both original comparison times are retained. -/
theorem prespectrumEndotransformationContraction_naturality
    {V W T U : Model.{u}} (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (h : F ≫ b = a ≫ G)
    (η : F.functor ⟶ F.functor) (θ : G.functor ⟶ G.functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X))
    (hθ : ∀ X, U.waldhausen.weq (θ.app X))
    (hz : ∀ X, W.waldhausen.weq ((modelZeroEndotransformation F).app X))
    (hz' : ∀ X, U.waldhausen.weq ((modelZeroEndotransformation G).app X))
    (he : whiskerRight η b.functor =
      eqToHom (congrArg Model.Hom.functor h) ≫ whiskerLeft a.functor θ ≫
        eqToHom (congrArg Model.Hom.functor h.symm))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumMap b).map n
        ((prespectrumEndotransformationContraction F η hη hz).level n (r, (s, x))) =
      (prespectrumEndotransformationContraction G θ hθ hz').level n
        (r, (s, (prespectrumMap a).map n x)) := by
  calc
    _ = (prespectrumEndotransformationContraction (V := V) (W := U) (F ≫ b)
        (coefficientPostwhiskerTyped (V := V) (W := W) (U := U) F b η)
        (coefficientPostwhiskerTyped_weak (V := V) (W := W) (U := U) F b η hη)
        (modelZeroEndotransformation_postcomp_weak
          (V := V) (W := W) (T := U) F hz b)).level n (r, (s, x)) :=
      (originalContractionPostTyped (V := V) (W := W) (U := U) F b η hη hz n r s x).symm
    _ = (prespectrumEndotransformationContraction (V := V) (W := U) (F ≫ b)
        (eqToHom (congrArg Model.Hom.functor h) ≫
          coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ ≫
            eqToHom (congrArg Model.Hom.functor h.symm))
        (coefficientPrewhiskerTyped_conjugate_weak
          (V := V) (W := W) (T := T) (U := U) F G a b h η θ hη he)
        (modelZeroEndotransformation_postcomp_weak
          (V := V) (W := W) (T := U) F hz b)).level n (r, (s, x)) :=
      originalCoefficientEndotransformationEqTyped
        (V := V) (W := W) (T := T) (U := U) F G a b h η θ hη hz he n r s x
    _ = (prespectrumEndotransformationContraction (V := V) (W := U) (a ≫ G)
        (coefficientPrewhiskerTyped (V := V) (T := T) (U := U) a G θ)
        (coefficientPrewhiskerTyped_weak (V := V) (T := T) (U := U) a G θ hθ)
        (modelZeroEndotransformation_precomp_weak
          (V := T) (W := U) (T := V) G hz' a)).level n (r, (s, x)) :=
      originalContractionCoefficientTransportTyped
        (V := V) (W := W) (T := T) (U := U) F G a b h η θ hη hθ hz hz' he n r s x
    _ = _ := originalContractionPreTyped (V := V) (T := T) (U := U) a G θ hθ hz' n r s x

end Quillen.Waldhausen.IteratedS
