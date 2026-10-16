/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.UnitTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BinaryNormalizationSimplex
public import Quillen.Waldhausen.SConstruction.Iterated.UnitPrismOriginalPastingLift

/-!
# The original precomposition unit track on six full references

An arbitrary unit on the target scheme acts through the actual prewhiskered geometric square
and original right-factor normalization pasting. All reference isomorphisms and the chosen
five-piece relative recipe are retained, including its initial source associator.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS.UnitPrismOriginalPastingLift
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.UnitTrackPrecompSimplex
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (r : (Γ(X, ⊤))ˣ)

/-- The actual source unit retains its original chosen-zero conjugation. -/
def sourceUnitIso : boundedFlatNormalizedPullback (f ≫ g) ≅
    boundedFlatNormalizedPullback (f ≫ g) :=
  (boundedFlatPullbackNormalizationIso (f ≫ g)).symm ≪≫
    boundedFlatPerfectPullbackUnitIso (f ≫ g) r ≪≫
      boundedFlatPullbackNormalizationIso (f ≫ g)

/-- The actual intermediate unit is normalized only after its original prewhiskering. -/
def middleUnitIso : BinaryNormalizationSimplex.intermediate f g ≅
    BinaryNormalizationSimplex.intermediate f g :=
  (Quillen.rebaseFunctorIso _ _ _ _).symm ≪≫
    isoWhiskerLeft (boundedFlatPerfectPullback g) (boundedFlatPerfectPullbackUnitIso f r) ≪≫
      Quillen.rebaseFunctorIso _ _ _ _

/-- The final unit prewhiskers the already normalized original target unit. -/
def finalUnitIso :
    boundedFlatNormalizedPullback g ⋙ boundedFlatNormalizedPullback f ≅
      boundedFlatNormalizedPullback g ⋙ boundedFlatNormalizedPullback f :=
  isoWhiskerLeft (boundedFlatNormalizedPullback g)
    ((boundedFlatPullbackNormalizationIso f).symm ≪≫ boundedFlatPerfectPullbackUnitIso f r ≪≫
      boundedFlatPullbackNormalizationIso f)

/-- This is precisely the original normalized source transformation. -/
theorem sourceUnitIso_hom : (sourceUnitIso f g r).hom =
    Waldhausen.normalizedWeakTransformation (boundedFlatPerfectPullback_exact (f ≫ g))
      (boundedFlatPerfectPullback_exact (f ≫ g))
      (boundedFlatPerfectPullbackUnitIso (f ≫ g) r).hom := rfl

/-- This is precisely the original normalized middle transformation. -/
theorem middleUnitIso_hom : (middleUnitIso f g r).hom =
    Waldhausen.normalizedWeakTransformation
      ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
      ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
      (whiskerLeft (boundedFlatPerfectPullback g)
        (boundedFlatPerfectPullbackUnitIso f r).hom) := rfl

/-- This is precisely the original final whiskered normalized transformation. -/
theorem finalUnitIso_hom : (finalUnitIso f g r).hom =
    whiskerLeft (boundedFlatNormalizedPullback g)
      (Waldhausen.normalizedWeakTransformation (boundedFlatPerfectPullback_exact f)
        (boundedFlatPerfectPullback_exact f) (boundedFlatPerfectPullbackUnitIso f r).hom) := rfl

/-- The original geometric intertwining survives the exact chosen-zero normalization. -/
theorem geometric_unit :
    (BinaryNormalizationSimplex.geometricIso f g).hom ≫ (middleUnitIso f g r).hom =
      (sourceUnitIso f g r).hom ≫ (BinaryNormalizationSimplex.geometricIso f g).hom := by
  rw [BinaryNormalizationSimplex.geometricIso_hom, middleUnitIso_hom, sourceUnitIso_hom]
  rw [← normalizedWeakTransformation_comp, ← normalizedWeakTransformation_comp]
  exact congrArg (Waldhausen.normalizedWeakTransformation
    (boundedFlatPerfectPullback_exact (f ≫ g))
    ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f)))
      (boundedFlatPerfectPullbackUnitIso_comp_target f g r)

/-- The original right normalization naturality square is the second unit equation. -/
theorem normalization_unit :
    (middleUnitIso f g r).hom ≫ (BinaryNormalizationSimplex.normalizationIso f g).hom =
      (BinaryNormalizationSimplex.normalizationIso f g).hom ≫ (finalUnitIso f g r).hom := by
  rw [middleUnitIso_hom, finalUnitIso_hom]
  exact exactNormalizationCompIso_natural_right (boundedFlatPerfectPullback_exact g)
    (boundedFlatPerfectPullback_exact f) (boundedFlatPerfectPullback_exact f)
    (boundedFlatPerfectPullbackUnitIso f r).hom

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

/-- The unchanged geometric component G of the original precomposition UnitTrack. -/
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
def sourceUnitTrack := boundedFlatPerfectUnitHomotopy (f ≫ g) r

/-- The unchanged normalized middle unit component B. -/
def middleUnitTrack := exactOriginalPrespectrumIsoHomotopy
  (boundedFlatPerfectWaldhausen Z) (boundedFlatPerfectWaldhausen X)
  ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
  ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
  (isoWhiskerLeft (boundedFlatPerfectPullback g) (boundedFlatPerfectPullbackUnitIso f r))

/-- The unchanged actual prewhiskered final unit component D. -/
def finalUnitTrack := Homotopy.precomp (boundedFlatPerfectPrespectrumMap g)
  (boundedFlatPerfectUnitHomotopy f r)

/-- The exact original geometric pasting JG, with its original equality certificate. -/
def geometricPasting := exactOriginalPrespectrumPastingHomotopy
  (boundedFlatPerfectWaldhausen Z) (boundedFlatPerfectWaldhausen X)
  (boundedFlatPerfectPullback_exact (f ≫ g))
  ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
  (boundedFlatPerfectPullback_exact (f ≫ g))
  ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
  (boundedFlatPerfectPullbackCompIso f g).hom
  (isoWhiskerLeft (boundedFlatPerfectPullback g) (boundedFlatPerfectPullbackUnitIso f r)).hom
  (boundedFlatPerfectPullbackUnitIso (f ≫ g) r).hom
  (boundedFlatPerfectPullbackCompIso f g).hom
  (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
  (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
  (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
  (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
  (boundedFlatPerfectPullbackUnitIso_comp_target f g r)

/-- The exact original normalization pasting JN, including its full native level transport. -/
def normalizationPasting := exactNormalizationRightTrackPasting
  (boundedFlatPerfectPullback_exact g) (boundedFlatPerfectPullback_exact f)
  (boundedFlatPerfectPullback_exact f) (boundedFlatPerfectPullbackUnitIso f r).hom
  (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)

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
            (isoWhiskerLeft (boundedFlatPerfectPullback g)
              (boundedFlatPerfectPullbackUnitIso f r)).hom) AsSmall.up))
        (fun A ↦ Waldhausen.normalizedWeakTransformation_weak
          (boundedFlatPerfectPullback_exact (f ≫ g))
          ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
          (boundedFlatPerfectPullbackCompIso f g).hom
          (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
          (AsSmall.down.obj A))
        (fun A ↦ Waldhausen.normalizedWeakTransformation_weak
          ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
          ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
          (isoWhiskerLeft (boundedFlatPerfectPullback g)
            (boundedFlatPerfectPullbackUnitIso f r)).hom
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
            (boundedFlatPerfectPullbackUnitIso (f ≫ g) r).hom) AsSmall.up))
        (whiskerLeft AsSmall.down (whiskerRight
          (Waldhausen.normalizedWeakTransformation
            (boundedFlatPerfectPullback_exact (f ≫ g))
            ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
            (boundedFlatPerfectPullbackCompIso f g).hom) AsSmall.up))
        (fun A ↦ Waldhausen.normalizedWeakTransformation_weak
          (boundedFlatPerfectPullback_exact (f ≫ g))
          (boundedFlatPerfectPullback_exact (f ≫ g))
          (boundedFlatPerfectPullbackUnitIso (f ≫ g) r).hom
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
      (isoWhiskerLeft (boundedFlatPerfectPullback g) (boundedFlatPerfectPullbackUnitIso f r)).hom
      (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
      (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)) := by
  exact exact_triangle_lift
    (boundedFlatPerfectWaldhausen Z) (boundedFlatPerfectWaldhausen X)
    (boundedFlatPerfectPullback_exact (f ≫ g))
    ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
    ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
    (boundedFlatPerfectPullbackCompIso f g).hom
    (isoWhiskerLeft (boundedFlatPerfectPullback g) (boundedFlatPerfectPullbackUnitIso f r)).hom
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
      (boundedFlatPerfectPullbackUnitIso (f ≫ g) r).hom
      (boundedFlatPerfectPullbackCompIso f g).hom
      (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
      (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)) := by
  exact exact_triangle_lift
    (boundedFlatPerfectWaldhausen Z) (boundedFlatPerfectWaldhausen X)
    (boundedFlatPerfectPullback_exact (f ≫ g))
    (boundedFlatPerfectPullback_exact (f ≫ g))
    ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
    (boundedFlatPerfectPullbackUnitIso (f ≫ g) r).hom
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
    (isoWhiskerLeft (boundedFlatPerfectPullback g) (boundedFlatPerfectPullbackUnitIso f r)).hom
    (boundedFlatPerfectPullbackUnitIso (f ≫ g) r).hom
    (boundedFlatPerfectPullbackCompIso f g).hom
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (boundedFlatPerfectPullbackUnitIso_comp_target f g r) (simplex f g r)
    (geometric_first_lift f g r) (geometric_second_lift f g r)

private theorem normalizationPasting_original_lift :
    HomotopyLift (simplex f g r) UnitPrismParameters.normalization
      (exactNormalizationRightPasting (boundedFlatPerfectPullback_exact g)
        (boundedFlatPerfectPullback_exact f) (boundedFlatPerfectPullback_exact f)
        (boundedFlatPerfectPullbackUnitIso f r).hom
        (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)) := by
  apply normalization_original_lift
  · exact UnitPrismNodes.normalization_first _ _ _ _ _ _ _ _
      (small_normalization_unit f g r)
  · exact UnitPrismNodes.normalization_second _ _ _ _ _ _ _ _

/-- Both individually ordered normalization triangles recover the original entire JN.
The original ofLevels endpoint transport changes neither of its independent coordinates. -/
theorem normalizationPasting_lift :
    HomotopyLift (simplex f g r) UnitPrismParameters.normalization
      (normalizationPasting f g r) :=
  normalization_right_track_lift (boundedFlatPerfectPullback_exact g)
    (boundedFlatPerfectPullback_exact f) (boundedFlatPerfectPullback_exact f)
    (boundedFlatPerfectPullbackUnitIso f r).hom
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (simplex f g r) (normalizationPasting_original_lift f g r)

/-- The chosen precomposition UnitTrack itself has the exact five-piece common-simplex lift.
All original associators, both original pastings and every relative time are retained. -/
theorem native_lift :
    HomotopyLift (simplex f g r) UnitPrismParameters.parameter
      (boundedFlatPerfectUnitTrackPrecomp f g r) :=
  UnitPrismParameters.parameter_lift (simplex f g r)
    (geometricTrack f g) (normalizationTrack f g) (sourceUnitTrack f g r)
    (middleUnitTrack f g r) (finalUnitTrack f g r)
    (geometricPasting f g r) (normalizationPasting f g r)
    (geometricPasting_lift f g r) (normalizationPasting_lift f g r)

end Quillen.PerfectComplexes.UnitTrackPrecompSimplex
