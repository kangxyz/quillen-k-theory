/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionModelTrackNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TripleTrack

/-!
# The original total geometric coefficient track

The Model coefficient comparison retains the actual normalized geometric comparison under the
original spectrum construction and the scheme coefficient-composition equality.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u v₀ u₀
namespace Quillen.PerfectComplexes

private theorem small_transport_heq {C D : Type u₀} [Category.{v₀} C] [Category.{v₀} D]
    {F F' G : C ⥤ D} (h : F = F') (η : F' ⟶ G) :
    HEq (whiskerLeft AsSmall.down.{v₀, u₀, 0} (whiskerRight (eqToHom h ≫ η) AsSmall.up.{v₀, u₀, 0}))
      (whiskerLeft AsSmall.down.{v₀, u₀, 0} (whiskerRight η AsSmall.up.{v₀, u₀, 0})) := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  rfl

/-- The actual Model binary coefficient track is the original total normalized geometric track. -/
theorem boundedFlatAffineOriginalCoefficientCompHomotopy_level
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (V := modelOf (boundedFlatPerfectWaldhausen (Spec R)))
      (W := modelOf (boundedFlatPerfectWaldhausen (Spec T)))
      (F := boundedFlatAffineOriginalCoefficientModelMap (f ≫ g))
      (G := boundedFlatAffineOriginalCoefficientModelMap f ≫
        boundedFlatAffineOriginalCoefficientModelMap g)
      (boundedFlatAffineOriginalCoefficientModelCompIso f g).hom
      (fun _ =>
        (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)).level n =
      (boundedFlatNormalizedCompTrack (Spec.map g) (Spec.map f)).level n := by
  rw [boundedFlatNormalizedCompTrack_level]
  apply prespectrumTransformationHomotopy_level_eq_of_heq
  · exact congrArg (fun p => modelMap (boundedFlatPerfectWaldhausen (Spec R))
      (boundedFlatPerfectWaldhausen (Spec T)) (boundedFlatNormalizedPullback_exact p)
      (boundedFlatNormalizedPullback_obj_zero p)) (Spec.map_comp f g)
  · exact (modelMap_comp (boundedFlatPerfectWaldhausen (Spec R))
      (boundedFlatPerfectWaldhausen (Spec S)) (boundedFlatPerfectWaldhausen (Spec T))
      (boundedFlatNormalizedPullback_exact (Spec.map f))
      (boundedFlatNormalizedPullback_exact (Spec.map g))
      (boundedFlatNormalizedPullback_obj_zero _) (boundedFlatNormalizedPullback_obj_zero _)).symm
  · change HEq
      (whiskerLeft AsSmall.down (whiskerRight
        (boundedFlatAffineNormalizedCoefficientCompIso f g).hom AsSmall.up)) _
    rw [boundedFlatAffineNormalizedCoefficientCompIso_hom]
    exact small_transport_heq (congrArg boundedFlatNormalizedPullback (Spec.map_comp f g))
      (boundedFlatNormalizedPullbackCompIso (Spec.map g) (Spec.map f)).hom

private theorem target_route_heq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (J : A ⥤ B) (F : B ⥤ D) (G : B ⥤ C) (H : C ⥤ D) (η : F ≅ G ⋙ H) :
    HEq ((isoWhiskerLeft J η ≪≫ (Functor.associator J G H).symm).hom)
      (whiskerLeft J η.hom) := by
  apply heq_of_eq
  ext X
  simp

/-- The actual target route retains original evaluation and the total geometric track. -/
theorem boundedFlatAffineSectionModelTargetHomotopy_level
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (V := boundedFlatAffineSectionModel R)
      (W := modelOf (boundedFlatPerfectWaldhausen (Spec T)))
      (F := boundedFlatAffineSectionEvaluationModelMap R ≫
        boundedFlatAffineOriginalCoefficientModelMap (f ≫ g))
      (G := (boundedFlatAffineSectionEvaluationModelMap R ≫
        boundedFlatAffineOriginalCoefficientModelMap f) ≫
          boundedFlatAffineOriginalCoefficientModelMap g)
      (boundedFlatAffineSectionModelTargetIso f g).hom
      (fun _ =>
        (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)).level n =
    (LoopPrespectrum.Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
      (boundedFlatNormalizedCompTrack (Spec.map g) (Spec.map f))).level n := by
  trans (prespectrumTransformationHomotopy
    (F := boundedFlatAffineSectionEvaluationModelMap R ≫
      boundedFlatAffineOriginalCoefficientModelMap (f ≫ g))
    (G := boundedFlatAffineSectionEvaluationModelMap R ≫
      (boundedFlatAffineOriginalCoefficientModelMap f ≫
        boundedFlatAffineOriginalCoefficientModelMap g))
    (whiskerLeft (boundedFlatAffineSectionEvaluationModelMap R).functor
      (boundedFlatAffineOriginalCoefficientModelCompIso f g).hom)
    (fun _ => (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)).level n
  · apply prespectrumTransformationHomotopy_level_eq_of_heq rfl (Category.assoc _ _ _)
    exact target_route_heq
      (boundedFlatAffineSectionEvaluationModelMap R).functor
      (boundedFlatAffineOriginalCoefficientModelMap (f ≫ g)).functor
      (boundedFlatAffineOriginalCoefficientModelMap f).functor
      (boundedFlatAffineOriginalCoefficientModelMap g).functor
      (boundedFlatAffineOriginalCoefficientModelCompIso f g)
  · rw [prespectrumTransformationHomotopy_precomp_level
      (F := boundedFlatAffineOriginalCoefficientModelMap (f ≫ g))
      (G := boundedFlatAffineOriginalCoefficientModelMap f ≫
        boundedFlatAffineOriginalCoefficientModelMap g)
      (boundedFlatAffineOriginalCoefficientModelCompIso f g).hom
      (fun _ => (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)
      (boundedFlatAffineSectionEvaluationModelMap R)]
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    exact DFunLike.congr_fun (boundedFlatAffineOriginalCoefficientCompHomotopy_level f g n)
      (s, (boundedFlatAffineSectionEvaluationPrespectrumMap R).map n x)

end Quillen.PerfectComplexes
