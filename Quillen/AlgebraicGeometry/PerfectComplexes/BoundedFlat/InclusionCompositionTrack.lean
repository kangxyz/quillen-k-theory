/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.InclusionCompositionNormalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.InclusionTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TripleTrack

/-!
# Whole composition compatibility of the original inclusion tracks

The normalized geometric inclusion equation is realized using actual transformation triangles.
Relative comparison with the original normalization tracks retains all cylinder parameters.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- The geometric composition square for the total normalized original inclusion tracks. -/
def boundedFlatNormalizedInclusionCompositionTrack {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] :
    (((boundedFlatNormalizedCompTrack f g).postcomp
      (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
        (boundedFlatPerfectInclusion_exact X))).trans
      ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap g)
        (boundedFlatNormalizedInclusionTrack f)).trans
        ((boundedFlatNormalizedInclusionTrack g).postcomp
          (perfectFlatPrespectrumMap f)))).RelHomotopy
    ((boundedFlatNormalizedInclusionTrack (f ≫ g)).trans
      (Homotopy.precomp (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Z)
        (perfectWaldhausen Z) (boundedFlatPerfectInclusion_exact Z))
        (perfectFlatNormalizedCompTrack f g))) := by
  let W := boundedFlatPerfectWaldhausen Z
  let V := perfectWaldhausen X
  let hf := boundedFlatNormalizedPullback_exact f
  let hg := boundedFlatNormalizedPullback_exact g
  let hfg := boundedFlatNormalizedPullback_exact (f ≫ g)
  let hix := boundedFlatNormalizedInclusion_exact X
  let hiy := boundedFlatNormalizedInclusion_exact Y
  let hiz := boundedFlatNormalizedInclusion_exact Z
  let hpf := perfectFlatNormalizedPullback_exact f
  let hpg := perfectFlatNormalizedPullback_exact g
  let hpfg := perfectFlatNormalizedPullback_exact (f ≫ g)
  let hA := hfg.comp hix
  let hB := (hg.comp hf).comp hix
  let hM := (hg.comp hiy).comp hpf
  let hD := hiz.comp hpfg
  let hC := (hiz.comp hpg).comp hpf
  let η := whiskerRight (boundedFlatNormalizedPullbackCompIso f g).hom
    (boundedFlatNormalizedInclusion X)
  let θ₁ := whiskerLeft (boundedFlatNormalizedPullback g)
    (boundedFlatNormalizedInclusionPullbackIso f).hom
  let θ₂ := whiskerRight (boundedFlatNormalizedInclusionPullbackIso g).hom
    (perfectFlatNormalizedPullback f)
  let η' := (boundedFlatNormalizedInclusionPullbackIso (f ≫ g)).hom
  let θ' := whiskerLeft (boundedFlatNormalizedInclusion Z)
    (perfectFlatNormalizedPullbackCompIso f g).hom
  have h0A : (boundedFlatNormalizedPullback (f ≫ g) ⋙ boundedFlatNormalizedInclusion X).obj
      W.zero = V.zero := by
    simp only [Functor.comp_obj, boundedFlatNormalizedPullback_obj_zero,
      boundedFlatNormalizedInclusion_obj_zero, W, V]
  have h0B : ((boundedFlatNormalizedPullback g ⋙ boundedFlatNormalizedPullback f) ⋙
      boundedFlatNormalizedInclusion X).obj W.zero = V.zero := by
    simp only [W, V, Functor.comp_obj, boundedFlatNormalizedPullback_obj_zero,
      boundedFlatNormalizedInclusion_obj_zero]
  have h0M : ((boundedFlatNormalizedPullback g ⋙ boundedFlatNormalizedInclusion Y) ⋙
      perfectFlatNormalizedPullback f).obj W.zero = V.zero := by
    simp only [W, V, Functor.comp_obj, boundedFlatNormalizedPullback_obj_zero,
      boundedFlatNormalizedInclusion_obj_zero, perfectFlatNormalizedPullback_obj_zero]
  have h0D : (boundedFlatNormalizedInclusion Z ⋙ perfectFlatNormalizedPullback (f ≫ g)).obj
      W.zero = V.zero := by
    simp only [W, V, Functor.comp_obj, boundedFlatNormalizedInclusion_obj_zero,
      perfectFlatNormalizedPullback_obj_zero]
  have h0C : ((boundedFlatNormalizedInclusion Z ⋙ perfectFlatNormalizedPullback g) ⋙
      perfectFlatNormalizedPullback f).obj W.zero = V.zero := by
    simp only [W, V, Functor.comp_obj, boundedFlatNormalizedInclusion_obj_zero,
      perfectFlatNormalizedPullback_obj_zero]
  let Hη := originalPrespectrumTransformationHomotopy W V hA hB h0A h0B η
    (fun _ ↦ V.weq_iso _ inferInstance)
  let Hθ₁ := originalPrespectrumTransformationHomotopy W V hB hM h0B h0M θ₁
    (fun _ ↦ V.weq_iso _ inferInstance)
  let Hθ₂ := originalPrespectrumTransformationHomotopy W V hM hC h0M h0C θ₂
    (fun _ ↦ V.weq_iso _ inferInstance)
  let Hη' := originalPrespectrumTransformationHomotopy W V hA hD h0A h0D η'
    (fun _ ↦ V.weq_iso _ inferInstance)
  let Hθ' := originalPrespectrumTransformationHomotopy W V hD hC h0D h0C θ'
    (fun _ ↦ V.weq_iso _ inferInstance)
  have J := originalPrespectrumPastingHomotopy W V hA hB hD hC h0A h0B h0D h0C
    η (θ₁ ≫ θ₂) η' θ' (fun _ ↦ V.weq_iso _ inferInstance)
    (fun _ ↦ V.weq_iso _ inferInstance) (fun _ ↦ V.weq_iso _ inferInstance)
    (fun _ ↦ V.weq_iso _ inferInstance) (boundedFlatNormalizedInclusionPullbackIso_comp f g)
  have T := originalPrespectrumTransformationCompositionHomotopy W V hB hM hC
    h0B h0M h0C θ₁ θ₂ (fun _ ↦ V.weq_iso _ inferInstance)
    (fun _ ↦ V.weq_iso _ inferInstance)
  have R : (Hη.trans (Hθ₁.trans Hθ₂)).RelHomotopy (Hη'.trans Hθ') :=
    ((Homotopy.RelHomotopy.refl Hη).hcomp T).symm.trans J
  apply Homotopy.RelHomotopy.ofLevels R
  · intro n
    apply Homotopy.trans_level_congr
    · rw [originalPrespectrumTransformationHomotopy_postcomp_level hfg (hg.comp hf) hix
        (boundedFlatNormalizedPullback_obj_zero _)
        ((congrArg (boundedFlatNormalizedPullback f).obj
          (boundedFlatNormalizedPullback_obj_zero g)).trans
          (boundedFlatNormalizedPullback_obj_zero f))
        (boundedFlatNormalizedInclusion_obj_zero X)
        (boundedFlatNormalizedPullbackCompIso f g).hom
        (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance) n]
      exact Homotopy.postcomp_level_congr _ _ _ n
        (boundedFlatNormalizedCompTrack_level f g n)
    · apply Homotopy.trans_level_congr
      · exact (originalPrespectrumTransformationHomotopy_precomp_level hg
          (hf.comp hix) (hiy.comp hpf) (boundedFlatNormalizedPullback_obj_zero g)
          _ _ (boundedFlatNormalizedInclusionPullbackIso f).hom
          (fun _ ↦ (perfectWaldhausen X).weq_iso _ inferInstance) n).symm
      · exact (originalPrespectrumTransformationHomotopy_postcomp_level
          (hg.comp hiy) (hiz.comp hpg) hpf _ _
          (perfectFlatNormalizedPullback_obj_zero f)
          (boundedFlatNormalizedInclusionPullbackIso g).hom
          (fun _ ↦ (perfectWaldhausen Y).weq_iso _ inferInstance) n).symm
  · intro n
    apply Homotopy.trans_level_congr
    · rfl
    · exact (originalPrespectrumTransformationHomotopy_precomp_level hiz
        hpfg (hpg.comp hpf) (boundedFlatNormalizedInclusion_obj_zero Z)
        (perfectFlatNormalizedPullback_obj_zero _) _
        (perfectFlatNormalizedPullbackCompIso f g).hom
        (fun _ ↦ (perfectWaldhausen X).weq_iso _ inferInstance) n).symm

/-- The original geometric composition and original inclusion normalization tracks satisfy the
whole pasting square. No compatibility track is supplied as a hypothesis. -/
def boundedFlatPerfectInclusionCompositionTrack {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] :
    (((boundedFlatPerfectPrespectrumCompHomotopy f g).postcomp
      (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
        (boundedFlatPerfectInclusion_exact X))).trans
      ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap g)
        (boundedFlatPerfectInclusionFlatPullbackHomotopy f)).trans
        ((boundedFlatPerfectInclusionFlatPullbackHomotopy g).postcomp
          (perfectFlatPrespectrumMap f)))).RelHomotopy
    ((boundedFlatPerfectInclusionFlatPullbackHomotopy (f ≫ g)).trans
      (Homotopy.precomp (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Z)
        (perfectWaldhausen Z) (boundedFlatPerfectInclusion_exact Z))
        (perfectFlatPrespectrumCompHomotopy f g))) :=
  (((boundedFlatNormalizedCompTrackComparison f g).symm.postcomp
    (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
      (boundedFlatPerfectInclusion_exact X))).hcomp
    ((Homotopy.RelHomotopy.precomp (boundedFlatPerfectPrespectrumMap g)
      (boundedFlatNormalizedInclusionTrackComparison f)).hcomp
      ((boundedFlatNormalizedInclusionTrackComparison g).postcomp
        (perfectFlatPrespectrumMap f)))).trans
    ((boundedFlatNormalizedInclusionCompositionTrack f g).trans
      ((boundedFlatNormalizedInclusionTrackComparison (f ≫ g)).symm.hcomp
        (Homotopy.RelHomotopy.precomp (exactOriginalPrespectrumMap
          (boundedFlatPerfectWaldhausen Z) (perfectWaldhausen Z)
          (boundedFlatPerfectInclusion_exact Z))
          (perfectFlatNormalizedCompTrackComparison f g))))

/-- Cancel the original geometric source track in the inclusion composition square, using its
actual reverse-track contraction. This is the orientation used by the Laurent chart boundaries. -/
def boundedFlatPerfectInclusionCompositionPasting {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] :
    ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap g)
      (boundedFlatPerfectInclusionFlatPullbackHomotopy f)).trans
      ((boundedFlatPerfectInclusionFlatPullbackHomotopy g).postcomp
        (perfectFlatPrespectrumMap f))).RelHomotopy
    (((boundedFlatPerfectPrespectrumCompHomotopy f g).postcomp
      (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
        (boundedFlatPerfectInclusion_exact X))).symm.trans
      ((boundedFlatPerfectInclusionFlatPullbackHomotopy (f ≫ g)).trans
        (Homotopy.precomp (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Z)
          (perfectWaldhausen Z) (boundedFlatPerfectInclusion_exact Z))
          (perfectFlatPrespectrumCompHomotopy f g)))) := by
  let D := (boundedFlatPerfectPrespectrumCompHomotopy f g).postcomp
    (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
      (boundedFlatPerfectInclusion_exact X))
  let A := (Homotopy.precomp (boundedFlatPerfectPrespectrumMap g)
    (boundedFlatPerfectInclusionFlatPullbackHomotopy f)).trans
    ((boundedFlatPerfectInclusionFlatPullbackHomotopy g).postcomp (perfectFlatPrespectrumMap f))
  exact (Homotopy.RelHomotopy.reflTrans A).symm.trans
    (((Homotopy.RelHomotopy.reflSymmTrans D).hcomp
      (Homotopy.RelHomotopy.refl A)).trans
      ((Homotopy.RelHomotopy.transAssoc D.symm D A).trans
        ((Homotopy.RelHomotopy.refl D.symm).hcomp
          (boundedFlatPerfectInclusionCompositionTrack f g))))

end Quillen.PerfectComplexes
