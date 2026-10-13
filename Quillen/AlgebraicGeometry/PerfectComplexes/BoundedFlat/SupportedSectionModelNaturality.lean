/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionComparison
public import Quillen.Topology.Prespectrum.HomotopyTransport
public import Quillen.Waldhausen.SmallModel.Whiskering
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopy

/-!
# Original supported coefficient comparison after chosen-zero normalization

The exact geometric pullback along the specified open-pair square has its canonical chosen-zero
normalization. The original supported evaluation comparison is pasted with the source and target
evaluation normalization isos and precisely the geometric pullback normalization iso. This gives
a whole prespectrum homotopy. No strict naturality of the
geometric evaluation maps is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)
attribute [local irreducible] boundedFlatAffineOriginalEvaluation
  boundedFlatAffineSupportedSectionEquivalence boundedFlatAffineSupportedEvaluation

/-- The original supported geometric coefficient pullback with its canonical zero normalization.
-/
def boundedFlatAffineSupportedOriginalCoefficientModelMap :
    modelOf (boundedFlatPerfectSupportedWaldhausen j) ⟶
      modelOf (boundedFlatPerfectSupportedWaldhausen j') :=
  modelMap _ _ (boundedFlatPerfectSupportedPullback_exact
    (boundedFlatAffineSupportedPairSquare j j' f l h)).rebase
    (Quillen.rebaseFunctor_obj_base _ _ _ _)

/-- The actual supported coefficient iso followed by the original normalization comparison. -/
def boundedFlatAffineSupportedSectionEvaluationCoefficientIso :
    (boundedFlatAffineSupportedSectionModelMap j j' f l h ≫
      boundedFlatAffineSupportedSectionEvaluationModelMap j').functor ≅
    (boundedFlatAffineSupportedSectionEvaluationModelMap j ≫
      boundedFlatAffineSupportedOriginalCoefficientModelMap j j' f l h).functor := by
  let F := boundedFlatPerfectSupportedPullback (boundedFlatAffineSupportedPairSquare j j' f l h)
  let hF := boundedFlatPerfectSupportedPullback_exact
    (boundedFlatAffineSupportedPairSquare j j' f l h)
  let i := smallModelWhiskerIso
    (C := BoundedFlatAffineSupportedSections j)
    (D := (boundedFlatPerfectSupported j).FullSubcategory)
    (E := (boundedFlatPerfectSupported j').FullSubcategory)
    (boundedFlatAffineSupportedEvaluation j)
    (boundedFlatAffineSupportedSectionsMap j j' f l h ⋙
      boundedFlatAffineSupportedEvaluation j') F _
    (boundedFlatAffineSupportedSectionCoefficientIso j j' f l h)
    (Quillen.rebaseFunctorIso F (boundedFlatPerfectSupportedWaldhausen j).zero
      (boundedFlatPerfectSupportedWaldhausen j').zero
      ((hF.zero (boundedFlatPerfectSupportedWaldhausen j).isZero).iso
        (boundedFlatPerfectSupportedWaldhausen j').isZero))
  change ((boundedFlatAffineSupportedSectionModelMap j j' f l h).functor ⋙
      (boundedFlatAffineSupportedSectionEvaluationModelMap j').functor) ≅
    ((boundedFlatAffineSupportedSectionEvaluationModelMap j).functor ⋙
      (boundedFlatAffineSupportedOriginalCoefficientModelMap j j' f l h).functor)
  exact Functor.isoWhiskerLeft (boundedFlatAffineSupportedSectionsMap j j' f l h)
      (boundedFlatAffineSupportedSectionEvaluationModelIso j').symm ≪≫
    (Functor.associator (boundedFlatAffineSupportedSectionsMap j j' f l h)
      (boundedFlatAffineSupportedEvaluation j') AsSmall.up).symm ≪≫ i ≪≫
    Functor.isoWhiskerRight (boundedFlatAffineSupportedSectionEvaluationModelIso j)
      (boundedFlatAffineSupportedOriginalCoefficientModelMap j j' f l h).functor

/-- Whole prespectrum naturality against the actual normalized supported coefficient map. -/
def boundedFlatAffineSupportedSectionEvaluationCoefficientHomotopy :
    LoopPrespectrum.Homotopy
      (boundedFlatAffineSupportedSectionPrespectrumMap j j' f l h ≫
        boundedFlatAffineSupportedSectionEvaluationPrespectrumMap j')
      (boundedFlatAffineSupportedSectionEvaluationPrespectrumMap j ≫
        prespectrumMap (boundedFlatAffineSupportedOriginalCoefficientModelMap j j' f l h)) :=
  (prespectrumTransformationHomotopy
    (V := boundedFlatAffineSupportedSectionModel j)
    (W := modelOf (boundedFlatPerfectSupportedWaldhausen j'))
    (F := boundedFlatAffineSupportedSectionModelMap j j' f l h ≫
      boundedFlatAffineSupportedSectionEvaluationModelMap j')
    (G := boundedFlatAffineSupportedSectionEvaluationModelMap j ≫
      boundedFlatAffineSupportedOriginalCoefficientModelMap j j' f l h)
    (boundedFlatAffineSupportedSectionEvaluationCoefficientIso j j' f l h).hom
    (fun s => (boundedFlatPerfectSupportedWaldhausen j').smallModel.weq_iso _ (by
      change IsIso
        ((boundedFlatAffineSupportedSectionEvaluationCoefficientIso j j' f l h).hom.app s)
      infer_instance))).cast
      (prespectrumFunctor.map_comp _ _) (prespectrumFunctor.map_comp _ _)

end Quillen.PerfectComplexes
