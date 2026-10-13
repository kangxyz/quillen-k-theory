/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NormalizedPullbackCoherence
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatPullback

/-! Compare the total normalized geometric transformation with the existing two-part track. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The original total normalized geometric comparison, with the literal raw map endpoints. -/
def boundedFlatNormalizedCompTrack {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Quillen.LoopPrespectrum.Homotopy (boundedFlatPerfectPrespectrumMap (f ≫ g))
      (boundedFlatPerfectPrespectrumMap g ≫ boundedFlatPerfectPrespectrumMap f) := by
  have H := originalPrespectrumTransformationHomotopy (boundedFlatPerfectWaldhausen Z)
    (boundedFlatPerfectWaldhausen X) (boundedFlatNormalizedPullback_exact (f ≫ g))
    ((boundedFlatNormalizedPullback_exact g).comp (boundedFlatNormalizedPullback_exact f))
    (boundedFlatNormalizedPullback_obj_zero _)
    ((congrArg (boundedFlatNormalizedPullback f).obj
      (boundedFlatNormalizedPullback_obj_zero g)).trans (boundedFlatNormalizedPullback_obj_zero f))
    (boundedFlatNormalizedPullbackCompIso f g).hom
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
  rw [originalPrespectrumMap_comp] at H
  exact H

/-- The existing geometric composition homotopy is relatively compared to the total original
normalized transformation by its actual composition triangle. -/
def boundedFlatNormalizedCompTrackComparison {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (boundedFlatNormalizedCompTrack f g).RelHomotopy
      (boundedFlatPerfectPrespectrumCompHomotopy f g) := by
  have homotopy_level_cast {X Y : Quillen.LoopPrespectrum}
      {f g g' : X ⟶ Y} (e : g = g')
      (p : Quillen.LoopPrespectrum.Homotopy f g = Quillen.LoopPrespectrum.Homotopy f g')
      (H : Quillen.LoopPrespectrum.Homotopy f g) (n : ℕ) :
      (p.mp H).level n = H.level n := by
    subst g'
    rfl
  let relativeOfLevels {E F : Quillen.LoopPrespectrum}
      {f g f' g' : E ⟶ F} {H K : Quillen.LoopPrespectrum.Homotopy f g}
      (J : H.RelHomotopy K) (H' K' : Quillen.LoopPrespectrum.Homotopy f' g')
      (hH : ∀ n, H'.level n = H.level n) (hK : ∀ n, K'.level n = K.level n) :
      H'.RelHomotopy K' := {
    level n := {
      toFun := J.level n
      continuous_toFun := (J.level n).continuous
      map_zero_left z := by simpa only [hH n] using (J.level n).apply_zero z
      map_one_left z := by simpa only [hK n] using (J.level n).apply_one z
      prop' r z hz := by
        change J.level n (r, z) = H'.level n z
        rw [hH n]
        exact (J.level n).eq_fst r hz }
    comm n r s x t := J.comm n r s x t }
  let W := boundedFlatPerfectWaldhausen Z
  let U := boundedFlatPerfectWaldhausen X
  let hfg := boundedFlatPerfectPullback_exact (f ≫ g)
  let hg := boundedFlatPerfectPullback_exact g
  let hf := boundedFlatPerfectPullback_exact f
  let η := Waldhausen.normalizedWeakTransformation hfg (hg.comp hf)
    (boundedFlatPerfectPullbackCompIso f g).hom
  let θ := (exactNormalizationCompIso hg hf).hom
  have J := originalPrespectrumTransformationCompositionHomotopy W U
    hfg.rebase (hg.comp hf).rebase (hg.rebase.comp hf.rebase)
    (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _)
    ((congrArg (boundedFlatNormalizedPullback f).obj
      (boundedFlatNormalizedPullback_obj_zero g)).trans (boundedFlatNormalizedPullback_obj_zero f))
    η θ (Waldhausen.normalizedWeakTransformation_weak _ _ _
      (fun _ ↦ U.weq_iso _ inferInstance)) (fun _ ↦ U.weq_iso _ inferInstance)
  have he : η ≫ θ = (boundedFlatNormalizedPullbackCompIso f g).hom :=
    (boundedFlatNormalizedPullbackCompIso_hom f g).symm
  simp only [he] at J
  apply relativeOfLevels J
  · intro n
    unfold boundedFlatNormalizedCompTrack
    apply homotopy_level_cast (originalPrespectrumMap_comp _ _ _
      (boundedFlatNormalizedPullback_exact g) (boundedFlatNormalizedPullback_exact f)
      (boundedFlatNormalizedPullback_obj_zero g) (boundedFlatNormalizedPullback_obj_zero f))
  · intro n
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    change (((exactOriginalPrespectrumIsoHomotopy _ _ hfg (hg.comp hf)
      (boundedFlatPerfectPullbackCompIso f g)).levelHomotopy n).trans
      ((exactOriginalPrespectrumMapCompHomotopy _ _ _ hg hf).levelHomotopy n)) (s, x) = _
    rw [ContinuousMap.HomotopyRel.trans_apply]
    change _ = (((originalPrespectrumTransformationHomotopy W U hfg.rebase
      (hg.comp hf).rebase _ _ η _).levelHomotopy n).trans
      ((originalPrespectrumTransformationHomotopy W U (hg.comp hf).rebase
      (hg.rebase.comp hf.rebase) _ _ θ _).levelHomotopy n)) (s, x)
    rw [ContinuousMap.HomotopyRel.trans_apply]
    split
    · rfl
    · exact DFunLike.congr_fun (exactOriginalPrespectrumMapCompHomotopy_level hg hf n) _

end Quillen.PerfectComplexes
