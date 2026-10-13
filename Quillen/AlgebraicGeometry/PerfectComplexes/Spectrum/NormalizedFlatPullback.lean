/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnit
public import Quillen.Waldhausen.SConstruction.Iterated.NormalizationPasting
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels
public import Quillen.Topology.Prespectrum.HomotopyTransport

/-!
# Total normalized perfect flat-pullback composition tracks

The original perfect geometric composition transformation followed by binary chosen-zero
normalization is compared, through its genuine transformation triangle, with the total normalized
isomorphism. Both constructions retain the original spectrum maps and full homotopy tracks.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
open Quillen.LoopPrespectrum
namespace Quillen.PerfectComplexes

/-- The exact chosen-zero normalization used by the original perfect flat-pullback map. -/
def perfectFlatNormalizedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    Perfect Y ⥤ Perfect X :=
  Quillen.rebaseFunctor (perfectFlatPullback f)
    (perfectWaldhausen Y).zero (perfectWaldhausen X).zero
    (((perfectFlatPullback_waldhausenExact f).zero (perfectWaldhausen Y).isZero).iso
      (perfectWaldhausen X).isZero)

/-- The unchanged canonical perfect flat-pullback normalization isomorphism. -/
def perfectFlatPullbackNormalizationIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    perfectFlatPullback f ≅ perfectFlatNormalizedPullback f := Quillen.rebaseFunctorIso _ _ _ _

/-- The total actual perfect geometric composition comparison after both binary normalizations. -/
def perfectFlatNormalizedPullbackCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Flat f] [Flat g] :
    perfectFlatNormalizedPullback (f ≫ g) ≅
      perfectFlatNormalizedPullback g ⋙ perfectFlatNormalizedPullback f :=
  (perfectFlatPullbackNormalizationIso (f ≫ g)).symm ≪≫ perfectFlatPullbackCompIso f g ≪≫
    isoWhiskerRight (perfectFlatPullbackNormalizationIso g) (perfectFlatPullback f) ≪≫
      isoWhiskerLeft _ (perfectFlatPullbackNormalizationIso f)

/-- The original perfect flat-pullback normalization is exact. -/
theorem perfectFlatNormalizedPullback_exact {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    Waldhausen.IsExact (perfectWaldhausen Y).cof (perfectWaldhausen Y).weq
      (perfectWaldhausen X).cof (perfectWaldhausen X).weq (perfectFlatNormalizedPullback f) :=
  (perfectFlatPullback_waldhausenExact f).rebase

/-- The original perfect normalization preserves its literal chosen zero. -/
@[simp] theorem perfectFlatNormalizedPullback_obj_zero {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (perfectFlatNormalizedPullback f).obj (perfectWaldhausen Y).zero =
      (perfectWaldhausen X).zero := Quillen.rebaseFunctor_obj_base _ _ _ _


/-- The total normalized geometric comparison is the composite of the two original
transformations. -/
theorem perfectFlatNormalizedPullbackCompIso_hom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] :
    (perfectFlatNormalizedPullbackCompIso f g).hom =
      Waldhausen.normalizedWeakTransformation (perfectFlatPullback_waldhausenExact (f ≫ g))
        ((perfectFlatPullback_waldhausenExact g).comp (perfectFlatPullback_waldhausenExact f))
        (perfectFlatPullbackCompIso f g).hom ≫
      (exactNormalizationCompIso (perfectFlatPullback_waldhausenExact g)
        (perfectFlatPullback_waldhausenExact f)).hom := by
  simp [perfectFlatNormalizedPullbackCompIso, perfectFlatPullbackNormalizationIso,
    Waldhausen.normalizedWeakTransformation, exactNormalizationCompIso, Category.assoc]
  rfl

/-- The original total perfect composition track has the unchanged geometric map endpoints. -/
def perfectFlatNormalizedCompTrack {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] :
    Homotopy (perfectFlatPrespectrumMap (f ≫ g))
      (perfectFlatPrespectrumMap g ≫ perfectFlatPrespectrumMap f) :=
  (originalPrespectrumTransformationHomotopy (perfectWaldhausen Z) (perfectWaldhausen X)
    (perfectFlatNormalizedPullback_exact (f ≫ g))
    ((perfectFlatNormalizedPullback_exact g).comp (perfectFlatNormalizedPullback_exact f))
    (perfectFlatNormalizedPullback_obj_zero _)
    ((congrArg (perfectFlatNormalizedPullback f).obj
      (perfectFlatNormalizedPullback_obj_zero g)).trans
      (perfectFlatNormalizedPullback_obj_zero f))
    (perfectFlatNormalizedPullbackCompIso f g).hom
    (fun _ ↦ (perfectWaldhausen X).weq_iso _ inferInstance)).cast rfl
      (originalPrespectrumMap_comp _ _ _ (perfectFlatNormalizedPullback_exact g)
        (perfectFlatNormalizedPullback_exact f) (perfectFlatNormalizedPullback_obj_zero g)
        (perfectFlatNormalizedPullback_obj_zero f))

/-- The total original transformation and the actual geometric-plus-binary track are relatively
compared by the original transformation triangle. -/
def perfectFlatNormalizedCompTrackComparison {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] :
    (perfectFlatNormalizedCompTrack f g).RelHomotopy (perfectFlatPrespectrumCompHomotopy f g) := by
  let W := perfectWaldhausen Z
  let U := perfectWaldhausen X
  let hfg := perfectFlatPullback_waldhausenExact (f ≫ g)
  let hg := perfectFlatPullback_waldhausenExact g
  let hf := perfectFlatPullback_waldhausenExact f
  let η := Waldhausen.normalizedWeakTransformation hfg (hg.comp hf)
    (perfectFlatPullbackCompIso f g).hom
  let θ := (exactNormalizationCompIso hg hf).hom
  have J := originalPrespectrumTransformationCompositionHomotopy W U
    hfg.rebase (hg.comp hf).rebase (hg.rebase.comp hf.rebase)
    (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _)
    ((congrArg (perfectFlatNormalizedPullback f).obj
      (perfectFlatNormalizedPullback_obj_zero g)).trans (perfectFlatNormalizedPullback_obj_zero f))
    η θ (Waldhausen.normalizedWeakTransformation_weak _ _ _
      (fun _ ↦ U.weq_iso _ inferInstance)) (fun _ ↦ U.weq_iso _ inferInstance)
  have he : η ≫ θ = (perfectFlatNormalizedPullbackCompIso f g).hom :=
    (perfectFlatNormalizedPullbackCompIso_hom f g).symm
  simp only [he] at J
  apply Homotopy.RelHomotopy.ofLevels J
  · intro n
    rfl
  · intro n
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    change (((exactOriginalPrespectrumIsoHomotopy _ _ hfg (hg.comp hf)
      (perfectFlatPullbackCompIso f g)).levelHomotopy n).trans
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
