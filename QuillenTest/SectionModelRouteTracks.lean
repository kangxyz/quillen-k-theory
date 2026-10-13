/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionModelTrackNaturality
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumTransformationTransport

/-! The original route tracks retain degree-zero loops and independent structure time. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open scoped unitInterval
universe u
namespace QuillenTest.SectionModelRouteTracks

open Quillen

/-- The first route retains the original degree-zero loop and its independent loop time. -/
theorem first_loop {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (s q : unitInterval) (γ : (prespectrum (boundedFlatAffineSectionModel R)).space 0) :
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec T))))
        (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec T)))) from
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
        (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)).level 0
        (s, γ)) q =
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec T))))
        (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec T)))) from
      (LoopPrespectrum.Homotopy.precomp
      (boundedFlatAffineSectionPrespectrumFunctor.map f)
      (boundedFlatAffineSectionEvaluationCoefficientHomotopy g)).level 0 (s, γ)) q := by
  rw [boundedFlatAffineSectionModelFirstRouteHomotopy_level]
  rfl

/-- The second route retains the original degree-zero loop and its independent loop time. -/
theorem second_loop {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (s q : unitInterval) (γ : (prespectrum (boundedFlatAffineSectionModel R)).space 0) :
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec T))))
        (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec T)))) from
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
        (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)).level 0
        (s, γ)) q =
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec T))))
        (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec T)))) from
      ((boundedFlatAffineSectionEvaluationCoefficientHomotopy f).postcomp
      (boundedFlatPerfectPrespectrumMap (Spec.map g))).level 0 (s, γ)) q := by
  rw [boundedFlatAffineSectionModelSecondRouteHomotopy_level]
  rfl

/-- Transport at both endpoints leaves the whole degree-zero loop unchanged. -/
theorem endpoint_loop {V W : Model.{u}} {F F' G' G : V ⟶ W}
    (hF : F = F') (hG : G' = G)
    (η : F'.functor ⟶ G'.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hη' : ∀ A, W.waldhausen.weq
      ((eqToHom (congrArg Model.Hom.functor hF) ≫ η ≫
        eqToHom (congrArg Model.Hom.functor hG)).app A))
    (s q : unitInterval) (γ : (prespectrum V).space 0) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from
      (prespectrumTransformationHomotopy
        (eqToHom (congrArg Model.Hom.functor hF) ≫ η ≫
          eqToHom (congrArg Model.Hom.functor hG)) hη').level 0 (s, γ)) q =
      (show Path (stagePoint 0 W) (stagePoint 0 W) from
        (prespectrumTransformationHomotopy η hη).level 0 (s, γ)) q := by
  rw [prespectrumTransformationHomotopy_transport_level hF hG η hη hη']

/-- Original homotopy time and suspension time are independent after strict source transport. -/
theorem first_structure {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (n : ℕ) (s t : unitInterval) (x : (prespectrum (boundedFlatAffineSectionModel R)).space n) :
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
        (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)).level (n + 1)
      (s, (prespectrum (boundedFlatAffineSectionModel R)).structureMap n x t) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen (Spec T)))).structureMap n
      ((LoopPrespectrum.Homotopy.precomp
      (boundedFlatAffineSectionPrespectrumFunctor.map f)
      (boundedFlatAffineSectionEvaluationCoefficientHomotopy g)).level n (s, x)) t := by
  rw [boundedFlatAffineSectionModelFirstRouteHomotopy_level]
  exact (LoopPrespectrum.Homotopy.precomp
      (boundedFlatAffineSectionPrespectrumFunctor.map f)
      (boundedFlatAffineSectionEvaluationCoefficientHomotopy g)).comm n s x t

end QuillenTest.SectionModelRouteTracks
