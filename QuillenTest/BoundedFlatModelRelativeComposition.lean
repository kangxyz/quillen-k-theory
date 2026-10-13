/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionModelRelativeComposition
/-! Actual geometric Model routes, the unchanged original loop, and three independent times. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open scoped unitInterval
universe u
namespace QuillenTest.BoundedFlatModelRelativeComposition

open Quillen

/-- The first route is exactly the original displayed two-track composite. -/
theorem first_route {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffineSectionModelCompositionRelHomotopy f g).at 0 =
      (prespectrumTransformationHomotopy
      (V := boundedFlatAffineSectionModel R)
      (W := modelOf (boundedFlatPerfectWaldhausen (Spec T)))
      (F := boundedFlatAffineSectionModelMap (f ≫ g) ≫ boundedFlatAffineSectionEvaluationModelMap T)
      (G := boundedFlatAffineSectionEvaluationModelMap R ≫
        boundedFlatAffineOriginalCoefficientModelMap (f ≫
        g))
      (boundedFlatAffineSectionEvaluationCoefficientIso (f ≫ g)).hom
      (fun _ => (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)).trans
        (prespectrumTransformationHomotopy
      (V := boundedFlatAffineSectionModel R)
      (W := modelOf (boundedFlatPerfectWaldhausen (Spec T)))
      (F := boundedFlatAffineSectionEvaluationModelMap R ≫
        boundedFlatAffineOriginalCoefficientModelMap (f ≫
        g))
      (G := (boundedFlatAffineSectionEvaluationModelMap R ≫
        boundedFlatAffineOriginalCoefficientModelMap f) ≫
        boundedFlatAffineOriginalCoefficientModelMap g)
      (boundedFlatAffineSectionModelTargetIso f g).hom
      (fun _ => (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)) :=
  (boundedFlatAffineSectionModelCompositionRelHomotopy f g).at_zero

/-- The second route is exactly the original displayed two-track composite. -/
theorem second_route {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffineSectionModelCompositionRelHomotopy f g).at 1 =
      (prespectrumTransformationHomotopy
      (V := boundedFlatAffineSectionModel R)
      (W := modelOf (boundedFlatPerfectWaldhausen (Spec T)))
      (F := boundedFlatAffineSectionModelMap (f ≫ g) ≫ boundedFlatAffineSectionEvaluationModelMap T)
      (G := (boundedFlatAffineSectionModelMap f ≫
        boundedFlatAffineSectionEvaluationModelMap S) ≫
        boundedFlatAffineOriginalCoefficientModelMap g)
      (boundedFlatAffineSectionModelFirstRouteIso f g).hom
      (fun _ => (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)).trans
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
      (fun _ => (boundedFlatPerfectWaldhausen (Spec T)).smallModel.weq_iso _ inferInstance)) :=
  (boundedFlatAffineSectionModelCompositionRelHomotopy f g).at_one

/-- The degree-zero value is the whole unchanged original coefficient loop. -/
theorem original_coefficient_loop {R S : CommRingCat.{u}} (f : R ⟶ S)
    (s q : unitInterval)
    (γ : Path (stagePoint 0 (boundedFlatAffineSectionModel R))
      (stagePoint 0 (boundedFlatAffineSectionModel R))) :
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec S))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec S)))) from
      (prespectrumTransformationHomotopy
      (V := boundedFlatAffineSectionModel R)
      (W := modelOf (boundedFlatPerfectWaldhausen (Spec S)))
      (F := boundedFlatAffineSectionModelMap f ≫ boundedFlatAffineSectionEvaluationModelMap S)
      (G := boundedFlatAffineSectionEvaluationModelMap R ≫
        boundedFlatAffineOriginalCoefficientModelMap f)
      (boundedFlatAffineSectionEvaluationCoefficientIso f).hom
      (fun _ => (boundedFlatPerfectWaldhausen (Spec S)).smallModel.weq_iso _ inferInstance)).level
        0 (s, γ)) q =
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec S))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec S)))) from
      (boundedFlatAffineSectionEvaluationCoefficientHomotopy f).level 0 (s, γ)) q := rfl

/-- Comparison, path and structure coordinates stay independent on the original prespectra. -/
theorem three_times {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (n : ℕ) (r s t : unitInterval)
    (x : (prespectrum (boundedFlatAffineSectionModel R)).space n) :
    (boundedFlatAffineSectionModelCompositionRelHomotopy f g).level (n + 1)
      (r, (s, (prespectrum (boundedFlatAffineSectionModel R)).structureMap n x t)) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen (Spec T)))).structureMap n
      ((boundedFlatAffineSectionModelCompositionRelHomotopy f g).level n (r, (s, x))) t :=
  (boundedFlatAffineSectionModelCompositionRelHomotopy f g).comm n r s x t

end QuillenTest.BoundedFlatModelRelativeComposition
