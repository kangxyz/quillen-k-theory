/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.InclusionNormalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ConeHomotopyComparison
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels
public import Quillen.Topology.Prespectrum.RelativeHomotopyReparam

/-!
# Whole original tracks for normalized bounded-flat inclusion

The total normalized inclusion isomorphism induces an actual based prespectrum homotopy. Its
comparison to the existing reversed-first, forward-second normalization track is constructed from
the original transformation triangle and explicit relative cancellation.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- The original normalized inclusion is exact for the two actual Waldhausen structures. -/
theorem boundedFlatNormalizedInclusion_exact (X : Scheme.{u}) :
    Waldhausen.IsExact (boundedFlatPerfectWaldhausen X).cof (boundedFlatPerfectWaldhausen X).weq
      (perfectWaldhausen X).cof (perfectWaldhausen X).weq (boundedFlatNormalizedInclusion X) :=
  (boundedFlatPerfectInclusion_exact X).rebase

/-- Normalization preserves the literal chosen zero of the inclusion. -/
@[simp] theorem boundedFlatNormalizedInclusion_obj_zero (X : Scheme.{u}) :
    (boundedFlatNormalizedInclusion X).obj (boundedFlatPerfectWaldhausen X).zero =
      (perfectWaldhausen X).zero := Quillen.rebaseFunctor_obj_base _ _ _ _

/-- The total normalized inclusion square is exactly the cancellation of the two original
binary normalizations, before either is realized. -/
theorem boundedFlatNormalizedInclusionPullbackIso_normalization {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] :
    (exactNormalizationCompIso (boundedFlatPerfectPullback_exact f)
      (boundedFlatPerfectInclusion_exact X)).hom ≫
      (boundedFlatNormalizedInclusionPullbackIso f).hom =
    (exactNormalizationCompIso (boundedFlatPerfectInclusion_exact Y)
      (perfectFlatPullback_waldhausenExact f)).hom := by
  apply NatTrans.ext
  funext K
  simp only [exactNormalizationCompIso, boundedFlatNormalizedInclusionPullbackIso,
    Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_inv, isoWhiskerLeft_inv, NatTrans.comp_app, whiskerRight_app,
    whiskerLeft_app, Category.assoc]
  change _ ≫ _ ≫ (boundedFlatInclusionNormalizationIso X).hom.app _ ≫
    (boundedFlatInclusionNormalizationIso X).inv.app _ ≫ _ = _
  rw [Iso.hom_inv_id_app_assoc]
  simp only [← map_comp_assoc]
  change _ ≫ (boundedFlatPerfectInclusion X).map
    ((boundedFlatPullbackNormalizationIso f).hom.app K ≫
      (boundedFlatPullbackNormalizationIso f).inv.app K) ≫ _ = _
  rw [Iso.hom_inv_id_app, map_id, Category.id_comp]
  rfl

/-- The original total normalized inclusion track, on the unchanged two composite maps. -/
def boundedFlatNormalizedInclusionTrack {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    Homotopy
      (boundedFlatPerfectPrespectrumMap f ≫ exactOriginalPrespectrumMap
        (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
        (boundedFlatPerfectInclusion_exact X))
      (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Y) (perfectWaldhausen Y)
        (boundedFlatPerfectInclusion_exact Y) ≫ perfectFlatPrespectrumMap f) :=
  (originalPrespectrumTransformationHomotopy (boundedFlatPerfectWaldhausen Y) (perfectWaldhausen X)
    ((boundedFlatNormalizedPullback_exact f).comp (boundedFlatNormalizedInclusion_exact X))
    ((boundedFlatNormalizedInclusion_exact Y).comp (perfectFlatNormalizedPullback_exact f))
    (by simp only [Functor.comp_obj, boundedFlatNormalizedPullback_obj_zero,
      boundedFlatNormalizedInclusion_obj_zero])
    (by simp only [Functor.comp_obj, boundedFlatNormalizedInclusion_obj_zero,
      perfectFlatNormalizedPullback_obj_zero])
    (boundedFlatNormalizedInclusionPullbackIso f).hom
    (fun _ ↦ (perfectWaldhausen X).weq_iso _ inferInstance)).cast
      (originalPrespectrumMap_comp _ _ _ (boundedFlatNormalizedPullback_exact f)
        (boundedFlatNormalizedInclusion_exact X) (boundedFlatNormalizedPullback_obj_zero f)
        (boundedFlatNormalizedInclusion_obj_zero X))
      (originalPrespectrumMap_comp _ _ _ (boundedFlatNormalizedInclusion_exact Y)
        (perfectFlatNormalizedPullback_exact f) (boundedFlatNormalizedInclusion_obj_zero Y)
        (perfectFlatNormalizedPullback_obj_zero f))

/-- The original two normalization tracks agree relatively with the actual total normalized
inclusion transformation; the inverse track is canceled by its genuine full parameter family. -/
def boundedFlatNormalizedInclusionTrackComparison {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (boundedFlatPerfectInclusionFlatPullbackHomotopy f).RelHomotopy
      (boundedFlatNormalizedInclusionTrack f) := by
  let W := boundedFlatPerfectWaldhausen Y
  let V := perfectWaldhausen X
  let hf := boundedFlatPerfectPullback_exact f
  let hi := boundedFlatPerfectInclusion_exact X
  let hj := boundedFlatPerfectInclusion_exact Y
  let hp := perfectFlatPullback_waldhausenExact f
  let η := (exactNormalizationCompIso hf hi).hom
  let θ := (boundedFlatNormalizedInclusionPullbackIso f).hom
  let α := (exactNormalizationCompIso hj hp).hom
  let h0 := Quillen.rebaseFunctor_obj_base
    (boundedFlatPerfectPullback f ⋙ boundedFlatPerfectInclusion X) W.zero V.zero
    (((hf.comp hi).zero W.isZero).iso V.isZero)
  let h1 := (congrArg (boundedFlatNormalizedInclusion X).obj
    (boundedFlatNormalizedPullback_obj_zero f)).trans (boundedFlatNormalizedInclusion_obj_zero X)
  let h2 := (congrArg (perfectFlatNormalizedPullback f).obj
    (boundedFlatNormalizedInclusion_obj_zero Y)).trans (perfectFlatNormalizedPullback_obj_zero f)
  let H1 := originalPrespectrumTransformationHomotopy W V (hf.comp hi).rebase
    (hf.rebase.comp hi.rebase) h0 h1 η (fun _ ↦ V.weq_iso _ inferInstance)
  let H2 := originalPrespectrumTransformationHomotopy W V (hf.comp hi).rebase
    (hj.rebase.comp hp.rebase) h0 h2 α (fun _ ↦ V.weq_iso _ inferInstance)
  let L := originalPrespectrumTransformationHomotopy W V (hf.rebase.comp hi.rebase)
    (hj.rebase.comp hp.rebase) h1 h2 θ (fun _ ↦ V.weq_iso _ inferInstance)
  have J := originalPrespectrumTransformationCompositionHomotopy W V (hf.comp hi).rebase
    (hf.rebase.comp hi.rebase) (hj.rebase.comp hp.rebase) h0 h1 h2 η θ
    (fun _ ↦ V.weq_iso _ inferInstance) (fun _ ↦ V.weq_iso _ inferInstance)
  have he : η ≫ θ = α := boundedFlatNormalizedInclusionPullbackIso_normalization f
  change (originalPrespectrumTransformationHomotopy W V (hf.comp hi).rebase
    (hj.rebase.comp hp.rebase) h0 h2 (η ≫ θ) _).RelHomotopy (H1.trans L) at J
  simp only [he] at J
  have R : (H1.symm.trans H2).RelHomotopy L :=
    ((Homotopy.RelHomotopy.refl H1.symm).hcomp J).trans
      ((Homotopy.RelHomotopy.transAssoc H1.symm H1 L).symm.trans
        (((Homotopy.RelHomotopy.reflSymmTrans H1).symm.hcomp
          (Homotopy.RelHomotopy.refl L)).trans (Homotopy.RelHomotopy.reflTrans L)))
  apply Homotopy.RelHomotopy.ofLevels R
  · intro n
    apply Homotopy.trans_level_congr
    · exact Homotopy.symm_level_congr _ _ n (exactOriginalPrespectrumMapCompHomotopy_level hf hi n)
    · exact exactOriginalPrespectrumMapCompHomotopy_level hj hp n
  · intro n
    rfl

/-- Equality of flat geometric arrows retains every level of the original inclusion track. -/
theorem boundedFlatPerfectInclusionFlatPullbackHomotopy_level_congr {X Y : Scheme.{u}}
    {f g : X ⟶ Y} [Flat f] [Flat g] (e : f = g) (n : ℕ) :
    (boundedFlatPerfectInclusionFlatPullbackHomotopy f).level n =
      (boundedFlatPerfectInclusionFlatPullbackHomotopy g).level n := by
  subst g
  rfl

end Quillen.PerfectComplexes
