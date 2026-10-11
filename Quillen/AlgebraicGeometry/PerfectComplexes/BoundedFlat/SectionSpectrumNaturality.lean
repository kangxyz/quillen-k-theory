/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatPullback
public import Quillen.Topology.Prespectrum.HomotopyTransport
public import Quillen.Waldhausen.SmallModel.Whiskering

/-!
# Original coefficient tracks for section evaluation

The actual cocartesian section transition compares strict coefficient restriction with original
geometric pullback. Its original normalization comparison supplies the whole prespectrum track.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The actual model morphism underlying original normalized coefficient pullback. -/
def boundedFlatAffineOriginalCoefficientModelMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    modelOf (boundedFlatPerfectWaldhausen (Spec R)) ⟶
      modelOf (boundedFlatPerfectWaldhausen (Spec S)) :=
  modelMap _ _ (boundedFlatPerfectPullback_exact (Spec.map f)).rebase
    (Quillen.rebaseFunctor_obj_base _ _ _ _)

/-- Actual evaluation and geometric pullback before spectrum normalization. -/
def boundedFlatAffineSectionCoefficientIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedFlatAffineSectionsMap f ⋙ boundedFlatAffineOriginalEvaluation S ≅
      boundedFlatAffineOriginalEvaluation R ⋙ boundedFlatPerfectPullback (Spec.map f) :=
  eqToIso (boundedFlatAffineSectionsMap_comp_evaluation f) ≪≫
    (boundedFlatAffineEvaluationPullbackIso R (Under.mk f)).symm

/-- The genuine section transition followed by the original chosen-zero comparison. -/
def boundedFlatAffineSectionEvaluationCoefficientIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedFlatAffineSectionModelMap f ≫
      boundedFlatAffineSectionEvaluationModelMap S).functor ≅
    (boundedFlatAffineSectionEvaluationModelMap R ≫
      boundedFlatAffineOriginalCoefficientModelMap f).functor := by
  let i := smallModelWhiskerIso
    (C := BoundedFlatAffineSections R)
    (D := BoundedFlatPerfect (Spec R)) (E := BoundedFlatPerfect (Spec S))
    (boundedFlatAffineOriginalEvaluation R)
    (boundedFlatAffineSectionsMap f ⋙ boundedFlatAffineOriginalEvaluation S)
    (boundedFlatPerfectPullback (Spec.map f)) _
    (boundedFlatAffineSectionCoefficientIso f)
    (Quillen.rebaseFunctorIso (boundedFlatPerfectPullback (Spec.map f))
      (boundedFlatPerfectWaldhausen (Spec R)).zero
      (boundedFlatPerfectWaldhausen (Spec S)).zero
      (((boundedFlatPerfectPullback_exact (Spec.map f)).zero
        (boundedFlatPerfectWaldhausen (Spec R)).isZero).iso
          (boundedFlatPerfectWaldhausen (Spec S)).isZero))
  change ((boundedFlatAffineSectionModelMap f).functor ⋙
      (boundedFlatAffineSectionEvaluationModelMap S).functor) ≅
    ((boundedFlatAffineSectionEvaluationModelMap R).functor ⋙
      (boundedFlatAffineOriginalCoefficientModelMap f).functor)
  rw [boundedFlatAffineSectionEvaluationModelMap_functor,
    boundedFlatAffineSectionEvaluationModelMap_functor]
  dsimp only [boundedFlatAffineSectionModelMap, boundedFlatAffineOriginalCoefficientModelMap,
    modelMap]
  exact (Functor.associator (boundedFlatAffineSectionsMap f)
    (boundedFlatAffineOriginalEvaluation S) AsSmall.up).symm ≪≫ i

/-- Whole naturality of original evaluation against the unchanged geometric coefficient map. -/
def boundedFlatAffineSectionEvaluationCoefficientHomotopy {R S : CommRingCat.{u}}
    (f : R ⟶ S) :
    LoopPrespectrum.Homotopy
      (boundedFlatAffineSectionPrespectrumFunctor.map f ≫
        boundedFlatAffineSectionEvaluationPrespectrumMap S)
      (boundedFlatAffineSectionEvaluationPrespectrumMap R ≫
        boundedFlatPerfectPrespectrumMap (Spec.map f)) :=
  (prespectrumTransformationHomotopy
    (V := boundedFlatAffineSectionModel R)
    (W := modelOf (boundedFlatPerfectWaldhausen (Spec S)))
    (F := boundedFlatAffineSectionModelMap f ≫ boundedFlatAffineSectionEvaluationModelMap S)
    (G := boundedFlatAffineSectionEvaluationModelMap R ≫
      boundedFlatAffineOriginalCoefficientModelMap f)
    (boundedFlatAffineSectionEvaluationCoefficientIso f).hom
    (fun _ => (boundedFlatPerfectWaldhausen (Spec S)).smallModel.weq_iso _ inferInstance)).cast
      (prespectrumFunctor.map_comp _ _) (prespectrumFunctor.map_comp _ _)

end Quillen.PerfectComplexes
