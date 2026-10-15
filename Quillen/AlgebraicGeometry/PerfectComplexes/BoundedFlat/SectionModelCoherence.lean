/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionEvaluationNormalization
public import Quillen.Waldhausen.SmallModel.CoefficientCoherence

/-!
# Original common-universe coefficient comparisons

The actual section evaluation comparisons are transported through the original `AsSmall` functors.
All coefficient maps and chosen-zero normalization isomorphisms remain unchanged.
-/
@[expose] public section

open Quillen.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The generic common-universe coefficient comparison at the original Model endpoints. -/
def boundedFlatAffineSectionLiftedCoefficientIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedFlatAffineSectionModelMap f ≫
      boundedFlatAffineSectionEvaluationModelMap S).functor ≅
    (boundedFlatAffineSectionEvaluationModelMap R ≫
      boundedFlatAffineOriginalCoefficientModelMap f).functor := by
  change ((boundedFlatAffineSectionModelMap f).functor ⋙
      (boundedFlatAffineSectionEvaluationModelMap S).functor) ≅
    ((boundedFlatAffineSectionEvaluationModelMap R).functor ⋙
      (boundedFlatAffineOriginalCoefficientModelMap f).functor)
  rw [boundedFlatAffineSectionEvaluationModelMap_functor,
    boundedFlatAffineSectionEvaluationModelMap_functor]
  dsimp only [boundedFlatAffineSectionModelMap, boundedFlatAffineOriginalCoefficientModelMap,
    modelMap]
  exact smallCoefficientIso boundedFlatAffinePseudofunctor f
    (boundedFlatPullbackNormalizationIso (Spec.map f))

/-- The smaller common-universe construction is exactly the unchanged original Model iso. -/
theorem boundedFlatAffineSectionLiftedCoefficientIso_eq {R S : CommRingCat.{u}}
    (f : R ⟶ S) :
    boundedFlatAffineSectionLiftedCoefficientIso f =
      boundedFlatAffineSectionEvaluationCoefficientIso f := by
  simp only [boundedFlatAffineSectionLiftedCoefficientIso,
    boundedFlatAffineSectionEvaluationCoefficientIso, smallCoefficientIso_eq,
    ← boundedFlatAffineSectionCoefficientIso_eq]
  rfl

/-- The unchanged Model coefficient track uses exactly the original normalized component. -/
theorem boundedFlatAffineSectionEvaluationCoefficientIso_hom_app
    {R S : CommRingCat.{u}} (f : R ⟶ S) (s : BoundedFlatAffineSections R) :
    (boundedFlatAffineSectionEvaluationCoefficientIso f).hom.app s =
      (AsSmall.up : BoundedFlatPerfect (Spec S) ⥤
        SmallModel (BoundedFlatPerfect (Spec S))).map
          ((Quillen.CategoryTheory.GrothendieckSections.normalizedCoefficientIso
            boundedFlatAffinePseudofunctor f
            (boundedFlatPullbackNormalizationIso (Spec.map f))).hom.app s) := by
  rw [← boundedFlatAffineSectionLiftedCoefficientIso_eq]
  exact smallCoefficientIso_hom_app boundedFlatAffinePseudofunctor f
    (boundedFlatPullbackNormalizationIso (Spec.map f)) s

/-- The original normalized geometric composition iso in the same small models as evaluation. -/
def boundedFlatAffineOriginalCoefficientModelCompIso {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffineOriginalCoefficientModelMap (f ≫ g)).functor ≅
      (boundedFlatAffineOriginalCoefficientModelMap f).functor ⋙
        (boundedFlatAffineOriginalCoefficientModelMap g).functor :=
  isoWhiskerLeft AsSmall.down
    (isoWhiskerRight (boundedFlatAffineNormalizedCoefficientCompIso f g) AsSmall.up)

end Quillen.PerfectComplexes
