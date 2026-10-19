/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationModelComposition
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TripleTrack
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopyNaturality
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumTransformationTransport
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels

/-!
# Original global evaluation and geometric composition tracks

The actual normalized Model pasting realizes to a relative homotopy between the two original
evaluation routes. The target route uses the original split geometric composition track,
not a replacement track. Every spectrum level and independent structure parameter is retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- The actual small-model target composition is the original total geometric track. -/
theorem evaluationRawCompHomotopy_level {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (V := modelOf (boundedFlatPerfectWaldhausen Z))
      (W := modelOf (boundedFlatPerfectWaldhausen X))
      (F := evaluationRawMap (f ≫ g)) (G := evaluationRawMap g ≫ evaluationRawMap f)
      (evaluationRawCompIso f g).hom
      (fun _ => (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)).level n =
      (boundedFlatNormalizedCompTrack f g).level n := by
  rw [boundedFlatNormalizedCompTrack_level]
  apply prespectrumTransformationHomotopy_level_eq_of_heq rfl
  · exact (modelMap_comp (boundedFlatPerfectWaldhausen Z)
      (boundedFlatPerfectWaldhausen Y) (boundedFlatPerfectWaldhausen X)
      (boundedFlatNormalizedPullback_exact g) (boundedFlatNormalizedPullback_exact f)
      (boundedFlatNormalizedPullback_obj_zero g) (boundedFlatNormalizedPullback_obj_zero f)).symm
  · rfl

private theorem first_route_heq
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    (J : A ⥤ B) (K : B ⥤ C) (L : A ⥤ C) (P : C ⥤ E)
    (M : B ⥤ D) (N : D ⥤ E) (h : L = J ⋙ K) (η : K ⋙ P ≅ M ⋙ N) :
    HEq ((eqToIso (congrArg (fun S => S ⋙ P) h) ≪≫
      Functor.associator J K P ≪≫ isoWhiskerLeft J η ≪≫
      (Functor.associator J M N).symm).hom) (whiskerLeft J η.hom) := by
  subst h
  apply heq_of_eq
  ext x
  simp

/-- Strict source transport retains every point of the original precomposed evaluation. -/
theorem evaluationCompositionFirstHomotopy_level {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (V := globalModel.obj (op Z)) (W := modelOf (boundedFlatPerfectWaldhausen X))
      (F := globalModel.map (f ≫ g).op ≫ evaluationModel (op X))
      (G := (globalModel.map g.op ≫ evaluationModel (op Y)) ≫ evaluationRawMap f)
      (evaluationCompositionFirstIso f g).hom
      (fun _ => (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)).level n =
      (Homotopy.precomp (prespectrumMap (globalModel.map g.op))
        (evaluationComparison f)).level n := by
  have hF : globalModel.map (f ≫ g).op ≫ evaluationModel (op X) =
      globalModel.map g.op ≫ (globalModel.map f.op ≫ evaluationModel (op X)) :=
    (congrArg (fun S => S ≫ evaluationModel (op X))
      (globalModel.map_comp g.op f.op)).trans (Category.assoc _ _ _)
  have hG := Category.assoc (globalModel.map g.op) (evaluationModel (op Y)) (evaluationRawMap f)
  trans (prespectrumTransformationHomotopy
    (F := globalModel.map g.op ≫ (globalModel.map f.op ≫ evaluationModel (op X)))
    (G := globalModel.map g.op ≫ (evaluationModel (op Y) ≫ evaluationRawMap f))
    (whiskerLeft (globalModel.map g.op).functor (evaluationComparisonIso f).hom)
    (fun _ => (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)).level n
  · apply prespectrumTransformationHomotopy_level_eq_of_heq hF hG
    exact first_route_heq (globalModel.map g.op).functor (globalModel.map f.op).functor
      (globalModel.map (f ≫ g).op).functor (evaluationModel (op X)).functor
      (evaluationModel (op Y)).functor (evaluationRawMap f).functor
      (globalReindex_comp f g) (evaluationComparisonIso f)
  · exact prespectrumTransformationHomotopy_precomp_level
      (F := globalModel.map f.op ≫ evaluationModel (op X))
      (G := evaluationModel (op Y) ≫ evaluationRawMap f) (evaluationComparisonIso f).hom
      (fun _ => (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)
      (globalModel.map g.op) n

/-- The second Model track retains the actual raw postcomposition of original evaluation. -/
theorem evaluationCompositionSecondHomotopy_level {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (V := globalModel.obj (op Z)) (W := modelOf (boundedFlatPerfectWaldhausen X))
      (F := (globalModel.map g.op ≫ evaluationModel (op Y)) ≫ evaluationRawMap f)
      (G := (evaluationModel (op Z) ≫ evaluationRawMap g) ≫ evaluationRawMap f)
      (evaluationCompositionSecondIso f g).hom
      (fun _ => (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)).level n =
      ((evaluationComparison g).postcomp (boundedFlatPerfectPrespectrumMap f)).level n :=
  prespectrumTransformationHomotopy_postcomp_level
    (F := globalModel.map g.op ≫ evaluationModel (op Y))
    (G := evaluationModel (op Z) ≫ evaluationRawMap g) (evaluationComparisonIso g).hom
    (fun _ => (boundedFlatPerfectWaldhausen Y).smallModel.weq_iso _ inferInstance)
    (evaluationRawMap f) n

private theorem target_route_heq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (J : A ⥤ B) (F : B ⥤ D) (G : B ⥤ C) (H : C ⥤ D) (η : F ≅ G ⋙ H) :
    HEq ((isoWhiskerLeft J η ≪≫ (Functor.associator J G H).symm).hom)
      (whiskerLeft J η.hom) := by
  apply heq_of_eq
  ext x
  simp

/-- The target Model track is original evaluation followed by total geometric composition. -/
theorem evaluationCompositionTargetHomotopy_level {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (V := globalModel.obj (op Z)) (W := modelOf (boundedFlatPerfectWaldhausen X))
      (F := evaluationModel (op Z) ≫ evaluationRawMap (f ≫ g))
      (G := (evaluationModel (op Z) ≫ evaluationRawMap g) ≫ evaluationRawMap f)
      (evaluationCompositionTargetIso f g).hom
      (fun _ => (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)).level n =
      (Homotopy.precomp (prespectrumMap (evaluationModel (op Z)))
        (boundedFlatNormalizedCompTrack f g)).level n := by
  trans (prespectrumTransformationHomotopy
    (F := evaluationModel (op Z) ≫ evaluationRawMap (f ≫ g))
    (G := evaluationModel (op Z) ≫ (evaluationRawMap g ≫ evaluationRawMap f))
    (whiskerLeft (evaluationModel (op Z)).functor (evaluationRawCompIso f g).hom)
    (fun _ => (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)).level n
  · apply prespectrumTransformationHomotopy_level_eq_of_heq rfl (Category.assoc _ _ _)
    exact target_route_heq (evaluationModel (op Z)).functor (evaluationRawMap (f ≫ g)).functor
      (evaluationRawMap g).functor (evaluationRawMap f).functor (evaluationRawCompIso f g)
  · rw [prespectrumTransformationHomotopy_precomp_level
      (F := evaluationRawMap (f ≫ g)) (G := evaluationRawMap g ≫ evaluationRawMap f)
      (evaluationRawCompIso f g).hom
      (fun _ => (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)
      (evaluationModel (op Z))]
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    exact DFunLike.congr_fun (evaluationRawCompHomotopy_level f g n)
      (s, (prespectrumMap (evaluationModel (op Z))).map n x)

/-- Original evaluation followed by total normalized geometric composition. -/
def evaluationCompositionTotalRoute {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Homotopy
      (prespectrumMap (globalModel.map (f ≫ g).op) ≫ prespectrumMap (evaluationModel (op X)))
      ((prespectrumMap (evaluationModel (op Z)) ≫ boundedFlatPerfectPrespectrumMap g) ≫
        boundedFlatPerfectPrespectrumMap f) :=
  ((evaluationComparison (f ≫ g)).trans
    (Homotopy.precomp (prespectrumMap (evaluationModel (op Z)))
      (boundedFlatNormalizedCompTrack f g))).cast rfl (Category.assoc _ _ _).symm

/-- Original evaluation followed by the unchanged two-part geometric composition track. -/
def evaluationCompositionSplitRoute {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Homotopy
      (prespectrumMap (globalModel.map (f ≫ g).op) ≫ prespectrumMap (evaluationModel (op X)))
      ((prespectrumMap (evaluationModel (op Z)) ≫ boundedFlatPerfectPrespectrumMap g) ≫
        boundedFlatPerfectPrespectrumMap f) :=
  ((evaluationComparison (f ≫ g)).trans
    (Homotopy.precomp (prespectrumMap (evaluationModel (op Z)))
      (boundedFlatPerfectPrespectrumCompHomotopy f g))).cast rfl (Category.assoc _ _ _).symm

/-- The other route retains both unchanged evaluation tracks and their original whiskering. -/
def evaluationCompositionWhiskeredRoute {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Homotopy
      (prespectrumMap (globalModel.map (f ≫ g).op) ≫ prespectrumMap (evaluationModel (op X)))
      ((prespectrumMap (evaluationModel (op Z)) ≫ boundedFlatPerfectPrespectrumMap g) ≫
        boundedFlatPerfectPrespectrumMap f) :=
  ((Homotopy.precomp (prespectrumMap (globalModel.map g.op)) (evaluationComparison f)).cast
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun S => S ≫ prespectrumMap (evaluationModel (op X)))
        ((GlobalSchemeLaurentTrack.diagram.map_comp g.op f.op).symm)))
    (Category.assoc _ _ _).symm).trans
      ((evaluationComparison g).postcomp (boundedFlatPerfectPrespectrumMap f))

/-- The actual Model comparison has exactly the two original total and whiskered routes. -/
def evaluationCompositionTotalWhiskered {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (evaluationCompositionTotalRoute f g).RelHomotopy
      (evaluationCompositionWhiskeredRoute f g) := by
  apply (evaluationModelCompositionRelHomotopy f g).ofLevels
  · intro n
    apply Homotopy.trans_level_congr
    · rfl
    · exact (evaluationCompositionTargetHomotopy_level f g n).symm
  · intro n
    apply Homotopy.trans_level_congr
    · exact (evaluationCompositionFirstHomotopy_level f g n).symm
    · exact (evaluationCompositionSecondHomotopy_level f g n).symm

/-- The genuine normalization triangle restores the existing split geometric target track. -/
def evaluationCompositionTotalSplit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (evaluationCompositionTotalRoute f g).RelHomotopy
      (evaluationCompositionSplitRoute f g) :=
  ((Homotopy.RelHomotopy.refl (evaluationComparison (f ≫ g))).hcomp
    (Homotopy.RelHomotopy.precomp (prespectrumMap (evaluationModel (op Z)))
      (boundedFlatNormalizedCompTrackComparison f g))).cast rfl (Category.assoc _ _ _).symm

/-- The whole original global evaluation composition relation, with no supplied filler. -/
def evaluationCompositionRelHomotopy {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (evaluationCompositionSplitRoute f g).RelHomotopy
      (evaluationCompositionWhiskeredRoute f g) :=
  (evaluationCompositionTotalSplit f g).symm.trans (evaluationCompositionTotalWhiskered f g)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
