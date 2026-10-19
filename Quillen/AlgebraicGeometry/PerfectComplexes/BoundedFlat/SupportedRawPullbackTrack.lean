/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedRawCharts
public import Quillen.Waldhausen.SConstruction.Iterated.NormalizationPasting
public import Quillen.Waldhausen.SConstruction.Iterated.OriginalTriangleTransport
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevelsEvaluation
public import Quillen.Topology.Prespectrum.HomotopyTransport

/-!
# Original split supported pullback tracks

The raw Model arrows realize to the original canonically normalized supported pullbacks.
Their composition uses the original supported geometric isomorphism followed by the original
binary normalization track. The total normalized chart transformation has a genuine relative
comparison with those two tracks, whose entire composition triangle is retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes.GlobalSupportedRawBass
open SupportedTensorEvaluation

/-- The original supported prespectrum of an actual open pair. -/
abbrev rawSpectrum (A : Scheme.OpenPairs.{u}) : LoopPrespectrum.{u+1} :=
  originalPrespectrum (boundedFlatPerfectSupportedWaldhausen A.obj.hom)

/-- Realize precisely the existing normalized geometric Model arrow. -/
abbrev rawMap {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B) : rawSpectrum B ⟶ rawSpectrum A :=
  prespectrumMap (evaluationRawMap p)

/-- Model realization is literally the original chosen-zero exact pullback map. -/
theorem rawMap_eq_original {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B) :
    rawMap p = exactOriginalPrespectrumMap _ _ (boundedFlatPerfectSupportedPullback_exact p) := rfl

/-- The two original composition tracks, with their original concatenation clock. -/
def compositionHomotopy {A B C : Scheme.OpenPairs.{u}} (p : A ⟶ B) (q : B ⟶ C) :
    Homotopy (rawMap (p ≫ q)) (rawMap q ≫ rawMap p) :=
  (exactOriginalPrespectrumIsoHomotopy _ _ (boundedFlatPerfectSupportedPullback_exact (p ≫ q))
    ((boundedFlatPerfectSupportedPullback_exact q).comp
      (boundedFlatPerfectSupportedPullback_exact p))
    (boundedFlatPerfectSupportedPullbackCompIso p q)).trans
    (exactOriginalPrespectrumMapCompHomotopy _ _ _
      (boundedFlatPerfectSupportedPullback_exact q) (boundedFlatPerfectSupportedPullback_exact p))

/-- The same original normalized geometric functor, before the common-universe lift. -/
abbrev normalizedPullback {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B) :=
  Quillen.rebaseFunctor (boundedFlatPerfectSupportedPullback p)
    (boundedFlatPerfectSupportedWaldhausen B.obj.hom).zero
    (boundedFlatPerfectSupportedWaldhausen A.obj.hom).zero
    (((boundedFlatPerfectSupportedPullback_exact p).zero
      (boundedFlatPerfectSupportedWaldhausen B.obj.hom).isZero).iso
      (boundedFlatPerfectSupportedWaldhausen A.obj.hom).isZero)

/-- The total original normalized supported composition isomorphism. -/
def normalizedCompositionIso {A B C : Scheme.OpenPairs.{u}} (p : A ⟶ B) (q : B ⟶ C) :
    normalizedPullback (p ≫ q) ≅ normalizedPullback q ⋙ normalizedPullback p :=
  (evaluationRawNormalization (p ≫ q)).symm ≪≫ boundedFlatPerfectSupportedPullbackCompIso p q ≪≫
    isoWhiskerRight (evaluationRawNormalization q) (boundedFlatPerfectSupportedPullback p) ≪≫
    isoWhiskerLeft _ (evaluationRawNormalization p)

/-- The chart API contains exactly this isomorphism after the original universe transport. -/
theorem normalizedCompositionIso_small {A B C : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : B ⟶ C) :
    isoWhiskerRight (isoWhiskerLeft AsSmall.down (normalizedCompositionIso p q)) AsSmall.up =
      chartNormalizationIso p q (p ≫ q) (boundedFlatPerfectSupportedPullbackCompIso p q) := rfl

/-- Cancellation of the intermediate normalization gives exactly the two original factors. -/
theorem normalizedCompositionIso_hom {A B C : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : B ⟶ C) :
    (normalizedCompositionIso p q).hom =
      normalizedWeakTransformation (boundedFlatPerfectSupportedPullback_exact (p ≫ q))
        ((boundedFlatPerfectSupportedPullback_exact q).comp
          (boundedFlatPerfectSupportedPullback_exact p))
        (boundedFlatPerfectSupportedPullbackCompIso p q).hom ≫
      (exactNormalizationCompIso (boundedFlatPerfectSupportedPullback_exact q)
        (boundedFlatPerfectSupportedPullback_exact p)).hom := by
  simp [normalizedCompositionIso, evaluationRawNormalization,
    normalizedWeakTransformation, exactNormalizationCompIso, Category.assoc]

/-- Realize the complete normalized chart transformation without a second normalization. -/
def normalizedCompositionHomotopy {A B C : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : B ⟶ C) :
    Homotopy (rawMap (p ≫ q)) (rawMap q ≫ rawMap p) :=
  (prespectrumTransformationHomotopy
    (F := evaluationRawMap (p ≫ q)) (G := evaluationRawMap q ≫ evaluationRawMap p)
    (chartNormalizationIso p q (p ≫ q) (boundedFlatPerfectSupportedPullbackCompIso p q)).hom
    (fun _ ↦ (rawModel A).waldhausen.weq_iso _ inferInstance)).cast rfl
      (prespectrumFunctor.map_comp (evaluationRawMap q) (evaluationRawMap p))

/-- The actual original composition triangle before retyping its two boundary tracks. -/
def compositionTriangle {A B C : Scheme.OpenPairs.{u}} (p : A ⟶ B) (q : B ⟶ C) :=
  show Homotopy.RelHomotopy (E := rawSpectrum C) (F := rawSpectrum A) _ _ from
  originalCompositionTransport (boundedFlatPerfectSupportedWaldhausen C.obj.hom)
    (boundedFlatPerfectSupportedWaldhausen A.obj.hom)
    (boundedFlatPerfectSupportedPullback_exact (p ≫ q)).rebase
    ((boundedFlatPerfectSupportedPullback_exact q).comp
      (boundedFlatPerfectSupportedPullback_exact p)).rebase
    ((boundedFlatPerfectSupportedPullback_exact q).rebase.comp
      (boundedFlatPerfectSupportedPullback_exact p).rebase)
    (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _)
    ((congrArg (normalizedPullback p).obj (Quillen.rebaseFunctor_obj_base _ _ _ _)).trans
      (Quillen.rebaseFunctor_obj_base _ _ _ _))
    (normalizedWeakTransformation (boundedFlatPerfectSupportedPullback_exact (p ≫ q))
      ((boundedFlatPerfectSupportedPullback_exact q).comp
        (boundedFlatPerfectSupportedPullback_exact p))
      (boundedFlatPerfectSupportedPullbackCompIso p q).hom)
    (exactNormalizationCompIso (boundedFlatPerfectSupportedPullback_exact q)
      (boundedFlatPerfectSupportedPullback_exact p)).hom
    (normalizedCompositionIso p q).hom
    (normalizedWeakTransformation_weak _ _ _
      (fun _ ↦ (boundedFlatPerfectSupportedWaldhausen A.obj.hom).weq_iso _ inferInstance))
    (fun _ ↦ (boundedFlatPerfectSupportedWaldhausen A.obj.hom).weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectSupportedWaldhausen A.obj.hom).weq_iso _ inferInstance)
    (normalizedCompositionIso_hom p q).symm

/-- The total normalized supported chart is relatively compared with the original split track. -/
def compositionComparison {A B C : Scheme.OpenPairs.{u}} (p : A ⟶ B) (q : B ⟶ C) :
    (normalizedCompositionHomotopy p q).RelHomotopy (compositionHomotopy p q) :=
  (compositionTriangle p q).ofLevels _ _ (fun _ => rfl) (fun n =>
    Homotopy.trans_level_congr _ _ _ _ n rfl
      (exactOriginalPrespectrumMapCompHomotopy_level
        (boundedFlatPerfectSupportedPullback_exact q)
        (boundedFlatPerfectSupportedPullback_exact p) n))

/-- The complete original boundary retyping, before taking any dependent level projection. -/
theorem compositionComparison_eq_original {A B C : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : B ⟶ C) :
    compositionComparison p q =
      (compositionTriangle p q).ofLevels (normalizedCompositionHomotopy p q)
        (compositionHomotopy p q) (fun _ => rfl) (fun n =>
          Homotopy.trans_level_congr _ _ _ _ n rfl
            (exactOriginalPrespectrumMapCompHomotopy_level
              (boundedFlatPerfectSupportedPullback_exact q)
              (boundedFlatPerfectSupportedPullback_exact p) n)) := rfl

/-- Retyping the boundaries changes none of the original triangle's two-time continuous map. -/
theorem compositionComparison_whole_level {A B C : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : B ⟶ C) (n : ℕ) :
    ((compositionComparison p q).level n).toContinuousMap =
      ((compositionTriangle p q).level n).toContinuousMap := by
  rw [compositionComparison_eq_original]
  exact Homotopy.RelHomotopy.ofLevels_whole_level (compositionTriangle p q) _ _ _ _ n

end Quillen.PerfectComplexes.GlobalSupportedRawBass
