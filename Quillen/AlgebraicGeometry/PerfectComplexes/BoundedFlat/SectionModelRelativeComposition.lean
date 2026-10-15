/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionModelPastingIdentification
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumPastingHomotopy
/-!
# Relative composition of the original Model coefficient comparisons

The genuine Model triangles compare the unchanged geometric coefficient routes, retaining the
actual strict-source transport and total normalized target comparison. Replacing the total target
track by the existing split geometric composition track, and the Bass seed comparison, are later
steps.
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

/-- The exact original Model transformation composites agree, retaining both endpoint transports. -/
theorem boundedFlatAffineSectionModelPasting_hom {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffineSectionEvaluationCoefficientIso (f ≫ g)).hom ≫
        (boundedFlatAffineSectionModelTargetIso f g).hom =
      (boundedFlatAffineSectionModelFirstRouteIso f g).hom ≫
        (boundedFlatAffineSectionModelSecondRouteIso f g).hom := by
  have hl : HEq
      ((boundedFlatAffineSectionEvaluationCoefficientIso (f ≫ g)).hom ≫
        (boundedFlatAffineSectionModelTargetIso f g).hom)
      ((smallCoefficientIso boundedFlatAffinePseudofunctor (f ≫ g)
          (boundedFlatPullbackNormalizationIso (Spec.map (f ≫ g)))).hom ≫
        (smallCoefficientTargetIso boundedFlatAffinePseudofunctor f g
          (boundedFlatPullbackNormalizationIso (Spec.map f))
          (boundedFlatPullbackNormalizationIso (Spec.map g))
          (boundedFlatPullbackNormalizationIso (Spec.map (f ≫ g)))).hom) :=
    heq_comp
      (by change (_ ⋙ (boundedFlatAffineSectionEvaluationModelMap T).functor) = _
          rw [boundedFlatAffineSectionEvaluationModelMap_functor]; rfl)
      (by change ((boundedFlatAffineSectionEvaluationModelMap R).functor ⋙
            (boundedFlatAffineOriginalCoefficientModelMap (f ≫ g)).functor) = _
          rw [boundedFlatAffineSectionEvaluationModelMap_functor,
            boundedFlatAffineOriginalCoefficientModelMap_functor]; rfl)
      (by rw [boundedFlatAffineSectionEvaluationModelMap_functor,
            boundedFlatAffineOriginalCoefficientModelMap_functor,
            boundedFlatAffineOriginalCoefficientModelMap_functor]; rfl)
      (boundedFlatAffineSectionEvaluationCoefficientIso_hom_heq (f ≫ g))
      (boundedFlatAffineSectionModelTargetIso_hom_heq f g)
  have hr : HEq
      ((boundedFlatAffineSectionModelFirstRouteIso f g).hom ≫
        (boundedFlatAffineSectionModelSecondRouteIso f g).hom)
      ((smallCoefficientFirstRouteIso boundedFlatAffinePseudofunctor f g
          (boundedFlatPullbackNormalizationIso (Spec.map g))).hom ≫
        (smallCoefficientSecondRouteIso boundedFlatAffinePseudofunctor f
          (Ng := boundedFlatNormalizedPullback (Spec.map g))
          (boundedFlatPullbackNormalizationIso (Spec.map f))).hom) :=
    heq_comp
      (by rw [boundedFlatAffineSectionEvaluationModelMap_functor]; rfl)
      (by rw [boundedFlatAffineSectionEvaluationModelMap_functor,
            boundedFlatAffineOriginalCoefficientModelMap_functor]; rfl)
      (by rw [boundedFlatAffineSectionEvaluationModelMap_functor,
            boundedFlatAffineOriginalCoefficientModelMap_functor,
            boundedFlatAffineOriginalCoefficientModelMap_functor]; rfl)
      (boundedFlatAffineSectionModelFirstRouteIso_hom_heq f g)
      (boundedFlatAffineSectionModelSecondRouteIso_hom_heq f g)
  exact eq_of_heq (hl.trans ((heq_of_eq
    (smallCoefficientPasting_hom boundedFlatAffinePseudofunctor f g
      (boundedFlatPullbackNormalizationIso (Spec.map f))
      (boundedFlatPullbackNormalizationIso (Spec.map g))
      (boundedFlatPullbackNormalizationIso (Spec.map (f ≫ g))))).trans hr.symm))

/-- A genuine two-parameter comparison of the original Model coefficient routes.
The first route uses the original composite-coefficient comparison and total target comparison;
the second retains strict source transport, the second coefficient, and the first coefficient
postwhiskered by original target pullback. -/
def boundedFlatAffineSectionModelCompositionRelHomotopy
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :=
  prespectrumPastingHomotopy
    (V := boundedFlatAffineSectionModel R)
    (W := modelOf (boundedFlatPerfectWaldhausen (Spec T)))
    (F := boundedFlatAffineSectionModelMap (f ≫ g) ≫
      boundedFlatAffineSectionEvaluationModelMap T)
    (G := boundedFlatAffineSectionEvaluationModelMap R ≫
      boundedFlatAffineOriginalCoefficientModelMap (f ≫ g))
    (G' := (boundedFlatAffineSectionModelMap f ≫
      boundedFlatAffineSectionEvaluationModelMap S) ≫
        boundedFlatAffineOriginalCoefficientModelMap g)
    (H := (boundedFlatAffineSectionEvaluationModelMap R ≫
      boundedFlatAffineOriginalCoefficientModelMap f) ≫
        boundedFlatAffineOriginalCoefficientModelMap g)
    (boundedFlatAffineSectionEvaluationCoefficientIso (f ≫ g)).hom
    (boundedFlatAffineSectionModelTargetIso f g).hom
    (boundedFlatAffineSectionModelFirstRouteIso f g).hom
    (boundedFlatAffineSectionModelSecondRouteIso f g).hom
    (fun _ => (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)
    (fun _ => (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)
    (fun _ => (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)
    (fun _ => (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)
    (boundedFlatAffineSectionModelPasting_hom f g)

end Quillen.PerfectComplexes
