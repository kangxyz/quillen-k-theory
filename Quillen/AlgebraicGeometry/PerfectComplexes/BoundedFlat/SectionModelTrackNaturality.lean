/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionModelRelativeComposition
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopyNaturality
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumTransformationTransport

/-!
# Original coefficient tracks inside the Model composition comparison

These full-level equalities identify the actual route tracks with the existing geometric
coefficient homotopies. The original coefficient, loop and structure parameters are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The last Model route is the unchanged coefficient track postcomposed by original pullback. -/
theorem boundedFlatAffineSectionModelSecondRouteHomotopy_level
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (V := boundedFlatAffineSectionModel R)
      (W := modelOf (boundedFlatPerfectWaldhausen (Spec T)))
      (F := (boundedFlatAffineSectionModelMap f ≫
        boundedFlatAffineSectionEvaluationModelMap S) ≫
          boundedFlatAffineOriginalCoefficientModelMap g)
      (G := (boundedFlatAffineSectionEvaluationModelMap R ≫
        boundedFlatAffineOriginalCoefficientModelMap f) ≫
          boundedFlatAffineOriginalCoefficientModelMap g)
      (boundedFlatAffineSectionModelSecondRouteIso f g).hom
      (fun _ =>
        (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)).level n =
    ((boundedFlatAffineSectionEvaluationCoefficientHomotopy f).postcomp
      (boundedFlatPerfectPrespectrumMap (Spec.map g))).level n := by
  exact prespectrumTransformationHomotopy_postcomp_level
    (F := boundedFlatAffineSectionModelMap f ≫ boundedFlatAffineSectionEvaluationModelMap S)
    (G := boundedFlatAffineSectionEvaluationModelMap R ≫
      boundedFlatAffineOriginalCoefficientModelMap f)
    (boundedFlatAffineSectionEvaluationCoefficientIso f).hom
    (fun _ => (boundedFlatPerfectWaldhausen (Spec S)).smallModel.weq_iso _ inferInstance)
    (boundedFlatAffineOriginalCoefficientModelMap g) n

private theorem first_route_heq
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    (J : A ⥤ B) (K : B ⥤ C) (L : A ⥤ C) (P : C ⥤ E)
    (M : B ⥤ D) (N : D ⥤ E) (h : L = J ⋙ K)
    (η : K ⋙ P ≅ M ⋙ N) :
    HEq ((eqToIso (congrArg (fun k => k ⋙ P) h) ≪≫
      Functor.associator J K P ≪≫ isoWhiskerLeft J η ≪≫
        (Functor.associator J M N).symm).hom)
      (whiskerLeft J η.hom) := by
  subst h
  apply heq_of_eq
  ext X
  simp

/-- Strict source composition and associators preserve the original prewhiskered track. -/
theorem boundedFlatAffineSectionModelFirstRouteHomotopy_level
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (V := boundedFlatAffineSectionModel R)
      (W := modelOf (boundedFlatPerfectWaldhausen (Spec T)))
      (F := boundedFlatAffineSectionModelMap (f ≫ g) ≫
        boundedFlatAffineSectionEvaluationModelMap T)
      (G := (boundedFlatAffineSectionModelMap f ≫
        boundedFlatAffineSectionEvaluationModelMap S) ≫
          boundedFlatAffineOriginalCoefficientModelMap g)
      (boundedFlatAffineSectionModelFirstRouteIso f g).hom
      (fun _ =>
        (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)).level n =
    (LoopPrespectrum.Homotopy.precomp
      (boundedFlatAffineSectionPrespectrumFunctor.map f)
      (boundedFlatAffineSectionEvaluationCoefficientHomotopy g)).level n := by
  have hF : boundedFlatAffineSectionModelMap (f ≫ g) ≫
      boundedFlatAffineSectionEvaluationModelMap T =
        boundedFlatAffineSectionModelMap f ≫ (boundedFlatAffineSectionModelMap g ≫
          boundedFlatAffineSectionEvaluationModelMap T) :=
    (congrArg (fun k => k ≫ boundedFlatAffineSectionEvaluationModelMap T)
      (boundedFlatAffineSectionModelFunctor.map_comp f g)).trans (Category.assoc _ _ _)
  have hG := Category.assoc (boundedFlatAffineSectionModelMap f)
    (boundedFlatAffineSectionEvaluationModelMap S)
    (boundedFlatAffineOriginalCoefficientModelMap g)
  trans (prespectrumTransformationHomotopy
    (F := boundedFlatAffineSectionModelMap f ≫ (boundedFlatAffineSectionModelMap g ≫
      boundedFlatAffineSectionEvaluationModelMap T))
    (G := boundedFlatAffineSectionModelMap f ≫ (boundedFlatAffineSectionEvaluationModelMap S ≫
      boundedFlatAffineOriginalCoefficientModelMap g))
    (whiskerLeft (boundedFlatAffineSectionModelMap f).functor
      (boundedFlatAffineSectionEvaluationCoefficientIso g).hom)
    (fun _ => (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)).level n
  · apply prespectrumTransformationHomotopy_level_eq_of_heq hF hG
    exact first_route_heq
      (boundedFlatAffineSectionModelMap f).functor
      (boundedFlatAffineSectionModelMap g).functor
      (boundedFlatAffineSectionModelMap (f ≫ g)).functor
      (boundedFlatAffineSectionEvaluationModelMap T).functor
      (boundedFlatAffineSectionEvaluationModelMap S).functor
      (boundedFlatAffineOriginalCoefficientModelMap g).functor
      (Quillen.CategoryTheory.StrictSections.underCocartesianReindex_comp
        boundedFlatAffineProjection f g)
      (boundedFlatAffineSectionEvaluationCoefficientIso g)
  · exact prespectrumTransformationHomotopy_precomp_level
      (F := boundedFlatAffineSectionModelMap g ≫ boundedFlatAffineSectionEvaluationModelMap T)
      (G := boundedFlatAffineSectionEvaluationModelMap S ≫
        boundedFlatAffineOriginalCoefficientModelMap g)
      (boundedFlatAffineSectionEvaluationCoefficientIso g).hom
      (fun _ => (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)
      (boundedFlatAffineSectionModelMap f) n

end Quillen.PerfectComplexes
