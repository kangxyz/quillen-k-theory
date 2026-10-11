/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionModelPasting
/-!
# Identifying the original Model coefficient routes

Whole-transformation transport identifies the original Model routes with their actual
common-universe constructions. Explicit functor equalities avoid expanding geometric components.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
private theorem transformation_hext {A B : Type*} [Category A] [Category B]
    {F G F' G' : A ⥤ B} (hF : F = F') (hG : G = G')
    (α : F ⟶ G) (β : F' ⟶ G') (h : ∀ x, HEq (α.app x) (β.app x)) : HEq α β := by
  subst hF
  subst hG
  apply heq_of_eq
  apply NatTrans.ext
  funext x
  exact eq_of_heq (h x)

/-- The target route is exactly the original lifted geometric comparison. -/
theorem boundedFlatAffineSectionModelTargetIso_hom_heq {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    HEq (boundedFlatAffineSectionModelTargetIso f g).hom
      (smallCoefficientTargetIso boundedFlatAffinePseudofunctor f g
        (boundedFlatPullbackNormalizationIso (Spec.map f))
        (boundedFlatPullbackNormalizationIso (Spec.map g))
        (boundedFlatPullbackNormalizationIso (Spec.map (f ≫ g)))).hom := by
  rfl

/-- The unchanged original evaluation comparison is the same lifted transformation. -/
theorem boundedFlatAffineSectionEvaluationCoefficientIso_hom_heq
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    HEq (boundedFlatAffineSectionEvaluationCoefficientIso f).hom
      (smallCoefficientIso boundedFlatAffinePseudofunctor f
        (boundedFlatPullbackNormalizationIso (Spec.map f))).hom := by
  apply transformation_hext
    (by change (_ ⋙ (boundedFlatAffineSectionEvaluationModelMap S).functor) = _
        rw [boundedFlatAffineSectionEvaluationModelMap_functor]; rfl)
    (by change ((boundedFlatAffineSectionEvaluationModelMap R).functor ⋙
          (boundedFlatAffineOriginalCoefficientModelMap f).functor) = _
        rw [boundedFlatAffineSectionEvaluationModelMap_functor,
          boundedFlatAffineOriginalCoefficientModelMap_functor]; rfl)
  intro s
  exact (heq_of_eq (boundedFlatAffineSectionEvaluationCoefficientIso_hom_app f s)).trans
    (heq_of_eq (smallCoefficientIso_hom_app boundedFlatAffinePseudofunctor f
      (boundedFlatPullbackNormalizationIso (Spec.map f)) s)).symm

/-- The first original route retains the exact strict source transport. -/
theorem boundedFlatAffineSectionModelFirstRouteIso_hom_heq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    HEq (boundedFlatAffineSectionModelFirstRouteIso f g).hom
      (smallCoefficientFirstRouteIso boundedFlatAffinePseudofunctor f g
        (boundedFlatPullbackNormalizationIso (Spec.map g))).hom := by
  unfold boundedFlatAffineSectionModelFirstRouteIso
  rw [← boundedFlatAffineSectionLiftedCoefficientIso_eq]
  rfl

private theorem whiskering_heq {A B C : Type*} [Category A] [Category B] [Category C]
    {F G F' G' : A ⥤ B} {J J' : B ⥤ C}
    (hF : F = F') (hG : G = G') (hJ : J = J')
    (α : F ⟶ G) (β : F' ⟶ G') (hα : HEq α β) :
    HEq (whiskerRight α J) (whiskerRight β J') := by
  subst hF
  subst hG
  subst hJ
  cases hα
  rfl

/-- The last original route retains the actual target coefficient functor. -/
theorem boundedFlatAffineSectionModelSecondRouteIso_hom_heq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    HEq (boundedFlatAffineSectionModelSecondRouteIso f g).hom
      (smallCoefficientSecondRouteIso boundedFlatAffinePseudofunctor f
        (Ng := boundedFlatNormalizedPullback (Spec.map g))
        (boundedFlatPullbackNormalizationIso (Spec.map f))).hom := by
  simp only [boundedFlatAffineSectionModelSecondRouteIso, smallCoefficientSecondRouteIso,
    isoWhiskerRight_hom]
  apply whiskering_heq
    (by change (_ ⋙ (boundedFlatAffineSectionEvaluationModelMap S).functor) = _
        rw [boundedFlatAffineSectionEvaluationModelMap_functor]; rfl)
    (by change ((boundedFlatAffineSectionEvaluationModelMap R).functor ⋙
          (boundedFlatAffineOriginalCoefficientModelMap f).functor) = _
        rw [boundedFlatAffineSectionEvaluationModelMap_functor,
          boundedFlatAffineOriginalCoefficientModelMap_functor]; rfl)
    (boundedFlatAffineOriginalCoefficientModelMap_functor g)
  exact boundedFlatAffineSectionEvaluationCoefficientIso_hom_heq f

end Quillen.PerfectComplexes
